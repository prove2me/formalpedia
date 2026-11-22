-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch288_Segment002
-- name    : Polychromatic418967fa_Branch288_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:02:35.809732+00:00
-- url     : https://prove2.me/theorems/ee0507c9-dc56-43e4-85c5-2f2af6da74a2
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch288_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_288_segment_002 : allB 179 288 :=
  allB_succ' 111 178 288 (Eq.refl Bool.true) (allA_succ_of_gcd 110 178 288 2 55 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 178 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 109 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 178 288 2 54 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 178 288 (accept_3_5 107 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 178 288 2 53 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 178 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 105 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 178 288 2 52 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 178 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 178 288 2 51 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 178 288 (accept_3_5 101 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 178 288 2 50 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 178 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 99 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 178 288 2 49 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 178 288
  (Polychromatic418967fa.accept_13_6_9_2_1_838 97 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 178 288 2 48 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 178 288 (accept_3_5 95 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 178 288 2 47 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 178 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 178 288 2 46 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 178 288
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 91 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 178 288 2 45 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 178 288 (accept_3_5 89 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 178 288 2 44 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 178 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 178 288 2 43 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 178 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 85 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 178 288 2 42 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 178 288 (accept_3_5 83 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 178 288 2 41 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 178 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 178 288 2 40 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 178 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 178 288 2 39 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 178 288 (accept_3_5 77 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 178 288 2 38 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 178 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 288 2 37 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 288
  (Polychromatic418967fa.accept_20_13_18_8_1_4936 73 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 178 288 2 36 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 178 288 (accept_3_5 71 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 288 2 35 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 69 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 288 2 34 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 288 2 33 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 288 (accept_3_5 65 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 288 2 32 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 288 2 31 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 288 2 30 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 288 (accept_3_5 59 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 288 2 29 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 288 2 28 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 288 2 27 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 288 (accept_3_5 53 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 288 2 26 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 288 2 25 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 288
  (Polychromatic418967fa.accept_21_7_10_15_1_8906 49 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 178 288 2 24 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 178 288 (accept_3_5 47 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 288 2 23 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 288 2 22 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 288
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 43 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 288 2 21 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 288 (accept_3_5 41 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 288 2 20 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 288 2 19 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 288 2 18 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 288 (accept_3_5 35 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 288 2 17 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 288 2 16 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 288 2 15 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 288 (accept_3_5 29 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 288 2 14 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 288 2 13 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 288 2 12 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 288 (accept_3_5 23 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 288 2 11 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 288 (Polychromatic418967fa.accept_20_1_18_8_1_6359 21 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 288 2 10 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 288 2 9 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 288 (accept_3_5 17 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 288 2 8 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 288 (Polychromatic418967fa.accept_19_15_7_3_1_4143 15 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 288 2 7 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 288
  (Polychromatic418967fa.accept_19_13_7_3_1_9798 13 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 288 2 6 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 288 (accept_3_5 11 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 288 2 5 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 178 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 288 2 4 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 288 2 3 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 288 (accept_3_5 5 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  288 2 2 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 178 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 288 2 1 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 178 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 177 288 (Eq.refl Bool.true) (allA_succ_of_gcd 111 177 288 3 37 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 177 288
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 110 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 177 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 109 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 177 288 3 36 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 177 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 107 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 177 288 (Polychromatic418967fa.accept_22_18_1_2_1_8505 106 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 177 288 3 35 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 177 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 104 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 177 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 103 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 177 288 3 34 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 177 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 177 288 (Polychromatic418967fa.accept_19_5_6_3_1_5578 100 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 177 288 3 33 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 177 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 177 288 3 32 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 177 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  95 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 177 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 94 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 177 288 3 31 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 177 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 92 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 177 288 3 30 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 177 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 89 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 177 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 88 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 177 288 3 29 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 177 288 (Polychromatic418967fa.accept_21_2_9_15_1_5747 86 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 177 288 3 28 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 177 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 82 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 177 288 3 27 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 177 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  79 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 177 288 3 26 59 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 177 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 177 288 3 25 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 177 288 (Polychromatic418967fa.accept_17_6_7_16_1_6836
  74 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 177 288 3 24 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 177 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 288
  (Polychromatic418967fa.accept_20_10_17_8_1_4856 70 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 177 288 3 23 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 177 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 68 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 177 288 3 22 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 177 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 288
  (Polychromatic418967fa.accept_19_7_6_3_1_6998 64 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 177 288 3 21 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 288
  (Polychromatic418967fa.accept_17_10_7_16_1_6841 61 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 177 288 3 20 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 177 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 177 288 3 19 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 288 (Polychromatic418967fa.accept_19_18_6_3_1_8405 56 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 177 288 3 18 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 177 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 53 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 177 288 3 17 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 177 288 (Polychromatic418967fa.accept_20_10_17_8_1_4856 50 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 288 3 16 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 288 3 15 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 288 (Polychromatic418967fa.accept_17_10_7_16_1_6841 44 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 177 288 3 14 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 288
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 40 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 288 3 13 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 288 3 12 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 288 3 11 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 288 3 10 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 177 288 3 9 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 177 288 (Polychromatic418967fa.accept_19_7_6_3_1_6998 26 177 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 177 288 3 8 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 177 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 177
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 288 3 7 59 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 288 3 6 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 288
  (Polychromatic418967fa.accept_19_16_6_3_1_6972 16 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 177 288 3 5 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 177 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 177 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 288 3 4 59 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 288
  (Polychromatic418967fa.accept_20_11_17_8_1_4903 11 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 177 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 177 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 288 3 3 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912
  8 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 177 288 3 2 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 288 (Polychromatic418967fa.accept_19_4_6_3_1_15078 4 177
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 288 3 1 59 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 177 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 177 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 176 288 (Eq.refl Bool.true) (allA_succ_of_gcd 112 176 288 16 7 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 176 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 111 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 176 288 2 55 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 176 288 (accept_3_4 109 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 176 288 4 27 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 176 288 (Polychromatic418967fa.accept_21_2_8_15_1_11906 107 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 176 288 2 53 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 176 288
  (Polychromatic418967fa.accept_19_10_5_3_1_13818 105 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 176 288 8 13 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 176 288 (accept_3_4 103 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 176 288 2 51 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 176 288 (Polychromatic418967fa.accept_19_6_5_3_1_11210 101 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 176 288 4 25 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 176 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 99 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 176 288 2 49 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 176 288 (accept_3_4 97 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 176 288 16 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 176 288 (Polychromatic418967fa.accept_17_10_6_16_1_6862 95 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 176 288 2 47 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 176 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 93 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 176 288 4 23 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 176 288 (accept_3_4 91 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 176 288 2 45 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 176 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 89 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 176 288 8 11 22 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 176 288
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 87 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 176 288 2 43 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 176 288 (accept_3_4 85 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 176 288 4 21 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 176 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 288 2 41 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 81 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 288 16 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 288 (accept_3_4 79 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 288 2 39 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280 77 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 288 4 19 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 75 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 288 2 37 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 288 (accept_3_4 73 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 288 8 9 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 176 288 (Polychromatic418967fa.accept_19_14_5_3_1_859 71 176 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 288 2 35 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 288 (Polychromatic418967fa.accept_21_6_8_15_1_8903
  69 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 176 288 4 17 44 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 176 288
  (accept_3_4 67 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 176 288 2 33 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 176 288
  (Polychromatic418967fa.accept_19_8_5_3_1_4181 65 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 176 288 16 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 176 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 176 288 2 31 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 176 288 (accept_3_4 61 176 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 176 288 4 15 44 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 176 288
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 176 288 2 29 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 176 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 288 8 7 22 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 288 (accept_3_4 55 176 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 288 2 27 88 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 176 288 4 13 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 176 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 176 288 2 25 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 176 288 (accept_3_4 49 176 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 176 288 16 3 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 176 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 176 288 2 23 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 176 288 (Polychromatic418967fa.accept_19_7_5_3_1_13861 45 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 176 288 4 11 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 176 288 (accept_3_4 43 176 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 176 288 2 21 88 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 176 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 41 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 176 288 8 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 176 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 39 176 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 176 288 2 19 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 176 288 (accept_3_4 37 176 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 176 288 4 9 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 176
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 288 2 17 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 288 16 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 288 (accept_3_4 31 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 288 2 15 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 288 4 7 44 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 288
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 176 288 2 13 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 176 288 (accept_3_4 25 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 288 8 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 176 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 176 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 288 2 11 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988
  21 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 288 4 5 44 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 288
  (accept_3_4 19 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 288 2 9 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 288
  (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 176 288 16 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 176 288 (Polychromatic418967fa.accept_26_15_20_2_1_12368 15 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 288 2 7 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 288 (accept_3_4 13 176 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 288 4 3 44 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 288
  (Polychromatic418967fa.accept_23_11_15_12_1_17807 11 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 176 288 2 5 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 176 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 288 8 1 22 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 288 (accept_3_4 7 176 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 288 2 3 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 5
  176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 288 4 1 44 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 288 2 1 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 288 (accept_3_4 1 176 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 175 288 (Eq.refl Bool.true) (allA_succ_of_accept 113 175 288 (accept_3_5 113 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 175 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 112 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 175 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 111 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 175 288 (accept_3_5 110 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 175 288 (Polychromatic418967fa.accept_27_1_13_18_1_17806 109 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 175 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 108 175 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 175 288 (accept_3_5 107 175 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 175 288
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 106 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 175 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 105 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 175 288 (accept_3_5 104 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 103 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 175 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 102 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 175 288 (accept_3_5 101 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 175 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 100 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 175 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 99 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 175 288 (accept_3_5 98 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 97 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 175 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 96 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 175 288 (accept_3_5 95 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 175 288 (Polychromatic418967fa.accept_19_18_4_3_1_4140 94 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 93 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 175 288 (accept_3_5 92 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 175 288 (Polychromatic418967fa.accept_22_3_21_2_1_17805 91 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 175 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 90 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 175 288 (accept_3_5 89 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 175 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 88 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 175 288 (accept_3_5 86 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 175 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 85 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 175 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 175 288 (accept_3_5 83 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 175 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 82 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 175 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 81 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 175 288 (accept_3_5 80 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 175 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 79 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 175 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 78 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 175 288 (accept_3_5 77 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 175 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 76 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 175 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 75 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 175 288 (accept_3_5 74 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 73 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 72 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 175 288 (accept_3_5 71 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 175 288 (Polychromatic418967fa.accept_17_2_5_16_1_1264 70 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 175 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 69 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 288 (accept_3_5 68 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 175 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 66 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 175 288 (accept_3_5 65 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 175 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 64 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 288 (accept_3_5 62 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 175 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 60 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 175 288 (accept_3_5 59 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 175 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 288 (accept_3_5 56 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 175 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 55 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 54 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 288 (accept_3_5 53 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 288 (accept_3_5 50 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 288 (accept_3_5 47 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 288 (Polychromatic418967fa.accept_19_8_4_3_1_5559 46 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 288 (accept_3_5 44 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 288 (accept_3_5 41 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 40 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 288 (accept_3_5 38 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 288
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 288 (accept_3_5 35 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 288 (accept_3_5 32 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 288 (Polychromatic418967fa.accept_21_10_7_15_1_8930 31 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 288 (accept_3_5 29 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 288 (accept_3_5 26 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 288 (accept_3_5 23 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 288 (accept_3_5 20 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 288 (Polychromatic418967fa.accept_17_2_5_16_1_1264 19 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 288
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 18 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 288 (accept_3_5 17 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 288 (Polychromatic418967fa.accept_19_16_4_3_1_2946 16 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 288 (accept_3_5 14 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 175
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 288 (accept_3_5 11 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 175 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 288 (accept_3_5 8 175 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 6 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 288 (accept_3_5 5 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 175 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 175 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 288 (accept_3_5 2 175 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 175 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 174 288 (Eq.refl Bool.true) (allA_succ_of_gcd 114 174 288 6 19 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 174 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 113 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 174 288 2 56 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 174 288 3 37 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 174 288 2 55 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 174 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 109 174
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 174 288 6 18 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 174 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 174 288 2 53 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 174 288 3 35 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 174 288 2 52 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 174 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 174
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 174 288 6 17 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 174 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 101 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 174 288 2 50 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 174 288 3 33 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 174 288 2 49 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 174 288
  (Polychromatic418967fa.accept_21_13_6_15_1_5818 97 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 174 288 6 16 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 174 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 95 174 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 174 288 2 47 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 174 288 3 31 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 174 288 2 46 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 174 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 91 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 288 6 15 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 174 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 174 288 2 44 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 174 288 3 29 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 174 288 2 43 87 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 174 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 85 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 288 6 14 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 83 174 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 174 288 2 41 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 174 288 3 27 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 174 288 2 40 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 288 6 13 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 174 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 288 2 38 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 174 288 3 25 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 174 288 2 37 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 73 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 288 6 12 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 288 (Polychromatic418967fa.accept_17_3_4_16_1_3208 71 174 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 288 2 35 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 174 288 3 23 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 174 288 2 34 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 67 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 288 6 11 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 174 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 288 2 32 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 174 288 3 21 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 288 2 31 87 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 288 6 10 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 174 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 288 2 29 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 174 288 3 19 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 288 2 28 87 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 55 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 288 6 9 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 174 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 288 2 26 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 288 3 17 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 288 2 25 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 288 6 8 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 288 2 23 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 288 3 15 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 288 2 22 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 288 6 7 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 288 (Polychromatic418967fa.accept_21_20_6_15_1_11937 41 174 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 288 2 20 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 288 3 13 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 288 2 19 87 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 288 6 6 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 288 2 17 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 288 3 11 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 288 2 16 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 288
  (Polychromatic418967fa.accept_21_10_6_15_1_8929 31 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 174 288 6 5 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 174 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 174 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 288 2 14 87 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 288 3 9 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 288 2 13 87 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 288 6 4 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 288 2 11 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 288 3 7 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 288 2 10 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 288 6 3 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 288 2 8 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 288 3 5 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 288 2 7 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 288 6 2 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 288 (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 174 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 288 2 5 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 288 3 3 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 288 2 4 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 288 6 1 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 174 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 288 2 2 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 288 3 1 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 288 2 1 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 288 (Polychromatic418967fa.accept_21_1_6_15_1_5742
  1 174 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 173 288 (Eq.refl Bool.true) (allA_succ_of_accept 115 173 288 (accept_3_4 115 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 173 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 114 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 173 288
  (Polychromatic418967fa.accept_19_18_2_3_1_4177 113 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 173 288 (accept_3_4 112 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 173 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 173 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 110 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 173 288 (accept_3_4 109 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 173 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 108 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 173 288 (Polychromatic418967fa.accept_19_12_2_3_1_11218 107 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 173 288 (accept_3_4 106 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 105 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 173 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 104 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 173 288 (accept_3_4 103 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 173 288 (accept_3_4 100 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 173 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 99 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 288
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 98 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 173 288 (accept_3_4 97 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 173 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 96 173 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 173 288 (accept_3_4 94 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 173 288 (Polychromatic418967fa.accept_11_5_8_2_1_588
  93 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 173 288
  (Polychromatic418967fa.accept_17_7_3_16_1_2208 92 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 173 288 (accept_3_4 91 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 173 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 89 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 173 288 (accept_3_4 88 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 288 (accept_3_4 85 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 84 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 288 (accept_3_4 82 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 173 288 (accept_3_4 79 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 173 288 (Polychromatic418967fa.accept_20_18_13_8_1_9398 78 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 288 (accept_3_4 76 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 288 (accept_3_4 73 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 288 (accept_3_4 70 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 288
  (Polychromatic418967fa.accept_19_11_2_3_1_8424 68 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 288 (accept_3_4 67 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 288 (accept_3_4 64 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 288 (accept_3_4 61 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 288 (accept_3_4 58 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 57 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 288 (accept_3_4 55 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 288 (accept_3_4 52 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 288 (accept_3_4 49 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 47 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 288 (accept_3_4 46 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 44 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 288 (accept_3_4 43 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 288 (accept_3_4 40 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 288 (accept_3_4 37 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 288 (accept_3_4 34 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 288 (Polychromatic418967fa.accept_21_12_5_15_1_17705 33
  173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 288 (accept_3_4 31 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 288 (Polychromatic418967fa.accept_21_8_5_15_1_4208 29 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 288 (accept_3_4 28 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 288 (accept_3_4 25 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 288 (Polychromatic418967fa.accept_20_3_13_8_1_12215 23 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 288 (accept_3_4 22 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 173
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 288 (accept_3_4 19 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 288 (accept_3_4 16 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 288
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 14 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 173 288 (accept_3_4 13 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 173 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 173 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 288 (accept_3_4 10 173 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 9
  173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 288
  (Polychromatic418967fa.accept_21_8_5_15_1_4208 8 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 288 (accept_3_4 7 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 288 (accept_3_4 4 173 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 173 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 288
  (Polychromatic418967fa.accept_25_2_23_13_1_17662 2 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 173 288 (accept_3_4 1 173 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  173
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 172 288 (Eq.refl Bool.true) (allA_succ_of_gcd 116 172 288 4 29 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 172 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 172 288 2 57 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 172 288 (accept_3_5 113 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 172 288 4 28 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 172 288 (Polychromatic418967fa.accept_19_16_1_3_1_7007 111 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 172 288 2 55 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 172 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 109 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 172 288 4 27 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 172 288 (accept_3_5 107 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 172 288 2 53 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 172 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 105 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 172 288 4 26 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 172 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 172 288 2 51 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 172 288 (accept_3_5 101 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 172 288 4 25 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 172 288 (Polychromatic418967fa.accept_17_14_2_16_1_4380 99 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 172 288 2 49 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 172 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 97 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 172 288 4 24 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 172 288 (accept_3_5 95 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 172 288 2 47 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 172 288 (Polychromatic418967fa.accept_17_8_2_16_1_5598 93 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 172 288 4 23 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 172 288
  (Polychromatic418967fa.accept_23_22_11_12_1_16205 91 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 172 288 2 45 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 172 288 (accept_3_5 89 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 172 288 4 22 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 172 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 172 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 172 288 2 43 86 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 172 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 172 288 4 21 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 288 (accept_3_5 83 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 288 2 41 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 81 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 288 4 20 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 288 2 39 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 288 (accept_3_5 77 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 288 4 19 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 172 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 288 2 37 86 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 288 4 18 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 288 (accept_3_5 71 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 288 2 35 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 288 (Polychromatic418967fa.accept_17_1_2_16_1_5596 69 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 288 4 17 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 288 2 33 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 288 (accept_3_5 65 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 288 4 16 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 288 2 31 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 288 4 15 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 288 (accept_3_5 59 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 288 2 29 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 288 4 14 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 288 2 27 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 288 (accept_3_5 53 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 288 4 13 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 288 2 25 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 288
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 288 4 12 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 288 (accept_3_5 47 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 288 2 23 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 172 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 288 4 11 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 288
  (Polychromatic418967fa.accept_19_5_1_3_1_8421 43 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 288 2 21 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 288 (accept_3_5 41 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 288 4 10 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 288 2 19 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 37 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 288 4 9 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 288 (accept_3_5 35 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 288 2 17 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 172 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 288 4 8 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31
  172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 288 2 15 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 288 (accept_3_5 29
  172 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 288 4 7 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 288 2 13 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 172 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 288 4 6 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 288 (accept_3_5 23 172 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 288 2 11 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216
  21 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 288 4 5 43 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 288 2 9 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 288 (accept_3_5 17 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 288 4 4 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 172 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 288 2 7 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 288
  (Polychromatic418967fa.accept_22_13_18_2_1_10024 13 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 172 288 4 3 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 172 288 (accept_3_5 11 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 288 2 5 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 172 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 288 4 2 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 288 (Polychromatic418967fa.accept_22_7_18_2_1_6810
  7 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 288 2 3 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 288 (accept_3_5 5
  172 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 288 4 1 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 172 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 288 2 1 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 172 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 171 288 (Eq.refl Bool.true) (allA_succ_of_gcd 117 171 288 9 13 19 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 171 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 116 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 171 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 115 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 171 288 3 38 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 171 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 113 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 171 288 (Polychromatic418967fa.accept_21_7_3_15_1_5800 112 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 171 288 3 37 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 171 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 110 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 171 288 9 12 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10
  107 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 171 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 106 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 171 288 3 35 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 171 288 (Polychromatic418967fa.accept_17_2_1_16_1_6946 104 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 171 288 3 34 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 171 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 101 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 171 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 100 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 171 288 9 11 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 171 288 (Polychromatic418967fa.accept_20_18_11_8_1_6367 98 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 171 288
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 97 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 171 288 3 32 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 288
  (Polychromatic418967fa.accept_21_10_3_15_1_13463 94 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 171 288 3 31 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 171 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 92 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 171 288 9 10 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 88
  171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 171 288 3 29 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 171 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 171 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 171 288 3 28 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 171 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  83 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 82 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 171 288 9 9 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 171 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 80 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 171 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 171 288 3 26 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 171 288
  (Polychromatic418967fa.accept_20_17_11_8_1_4894 77 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 171 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 76 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 171 288 3 25 57 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 171 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 73 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 171 288 9 8 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 171 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  71 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 171 288 3 23 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 171 288 3 22 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 171 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 171 288 (Polychromatic418967fa.accept_21_1_3_15_1_5797 64 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 171 288 9 7 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 171 288
  (Polychromatic418967fa.accept_25_12_21_13_1_17674 62 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 288 3 20 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 59 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 288 3 19 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  56 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 288 9 6 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 288 (Polychromatic418967fa.accept_21_10_3_15_1_13463 52
  171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 288 3 17 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 50 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 171 288 3 16 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47
  171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 46 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 288 9 5 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 171
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 288 3 14 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 288 3 13 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 288
  (Polychromatic418967fa.accept_20_18_11_8_1_6367 38 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 288 9 4 19 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 35 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 288 (Polychromatic418967fa.accept_25_9_21_13_1_17804 34 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 288 3 11 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 288 3 10 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 288 (Polychromatic418967fa.accept_10_9_1_8_1_755
  29 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 288
  (Polychromatic418967fa.accept_21_7_3_15_1_5800 28 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 171 288 9 3 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 171 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 288 3 8 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 288 (Polychromatic418967fa.accept_17_5_1_16_1_4359 22 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 288 3 7 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 288 (Polychromatic418967fa.accept_15_5_6_3_1_525
  20 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 171 288 9 2 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 17 171 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 288 3 5 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 288
  (Polychromatic418967fa.accept_21_14_3_15_1_16315 14 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 171 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 171 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 288 3 4 57 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 288 9 1 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 288 (Polychromatic418967fa.accept_21_8_3_15_1_2875 8 171 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 288
  (Polychromatic418967fa.accept_21_7_3_15_1_5800 7 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 288 3 2 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 171 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 288 3 1 57 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 171 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 171 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 170 288 (Eq.refl Bool.true) (allA_succ_of_gcd 118 170 288 2 59 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 170 288
  (Polychromatic418967fa.accept_20_17_10_8_1_9374 117 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 170 288 2 58 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 170 288 (accept_3_4 115 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 170 288 2 57 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 170 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 113 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 170 288 2 56 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 170 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 111 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 170 288 2 55 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 170 288 (accept_3_4 109 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 170 288 2 54 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 170 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 107 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 170 288 2 53 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 170 288
  (Polychromatic418967fa.accept_20_5_10_8_1_6397 105 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 170 288 2 52 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 170 288 (accept_3_4 103 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 170 288 2 51 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 170 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 170 288 2 50 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 170 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 99 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 170 288 2 49 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 170 288 (accept_3_4 97 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 170 288 2 48 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 170 288 (Polychromatic418967fa.accept_20_15_10_8_1_6398 95 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 170 288 2 47 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 170 288
  (Polychromatic418967fa.accept_21_9_2_15_1_1622 93 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 170 288 2 46 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 170 288 (accept_3_4 91 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 170 288 2 45 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 170 288 (Polychromatic418967fa.accept_23_20_9_12_1_16227 89 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 288 2 44 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 288 2 43 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 170 288 (accept_3_4 85 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 170 288 2 42 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 170 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 170 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 288 2 41 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 81 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 288 2 40 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 288 (accept_3_4 79 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 288 2 39 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 77 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 288 2 38 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 288
  (Polychromatic418967fa.accept_20_15_10_8_1_6398 75 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 170 288 2 37 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 170 288 (accept_3_4 73 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 288 2 36 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 71 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 288 2 35 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 288 2 34 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 288 (accept_3_4 67 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 288 2 33 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 65 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 288 2 32 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 288 2 31 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 288 (accept_3_4 61 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 288 2 30 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 170 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 288 2 29 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 288 2 28 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 288 (accept_3_4 55 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 288 2 27 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 53 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 288 2 26 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 288
  (Polychromatic418967fa.accept_13_12_1_2_1_845 51 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 288 2 25 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 288 (accept_3_4 49 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 288 2 24 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 288 (Polychromatic418967fa.accept_15_2_5_3_1_552 47 170 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 288 2 23 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 288 2 22 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 288 (accept_3_4 43 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 288 2 21 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 170 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 288 2 20 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 288
  (Polychromatic418967fa.accept_15_9_5_3_1_554 39 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 288 2 19 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 288 (accept_3_4 37 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 288 2 18 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 288 2 17 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 288
  (Polychromatic418967fa.accept_19_14_18_3_1_12569 33 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 170 288 2 16 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 170 288 (accept_3_4 31 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 288 2 15 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 288 2 14 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 288 2 13 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 288 (accept_3_4 25 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 288 2 12 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 288 2 11 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 288
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 288 2 10 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 288 (accept_3_4 19 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 288 2 9 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 170 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 288 2 8 85 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 15 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 288 2 7 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 288 (accept_3_4 13 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 288 2 6 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 288 (Polychromatic418967fa.accept_19_11_18_3_1_1755 11 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 288 2 5 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 288 2 4 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 288 (accept_3_4 7 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  288 2 3 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 5 170 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 288 2 2 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 170 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 288 2 1 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 288 (accept_3_4 1 170 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 169 288 (Eq.refl Bool.true) (allA_succ_of_accept 119 169 288 (accept_3_5 119 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 169 288 (Polychromatic418967fa.accept_22_8_15_2_1_8515 118
  169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 169 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 117 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 169 288 (accept_3_5 116 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 169 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 115 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 114 169 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 169 288 (accept_3_5 113 169 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 169 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 112 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 111 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 169 288 (accept_3_5 110 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 169 288 (Polychromatic418967fa.accept_19_14_17_3_1_4137 109 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 169 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 108 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 169 288 (accept_3_5 107 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 169 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 106 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 169 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 105 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 169 288 (accept_3_5 104 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 169 288 (Polychromatic418967fa.accept_19_8_17_3_1_4154 103
  169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 169 288
  (Polychromatic418967fa.accept_21_18_1_15_1_11930 102 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 169 288 (accept_3_5 101 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 169 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 100 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 99 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 169 288 (accept_3_5 98 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 169 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 97 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 169 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 96 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 288 (accept_3_5 95 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 94 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 288
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 93 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 288 (accept_3_5 92 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 91 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 169 288 (Polychromatic418967fa.accept_19_14_17_3_1_4137 90 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 288 (accept_3_5 89 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 288 (Polychromatic418967fa.accept_19_12_17_3_1_5515 88 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 87 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 169 288 (accept_3_5 86 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 169 288 (Polychromatic418967fa.accept_25_10_19_13_1_16087 85 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 288 (accept_3_5 83 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 82 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 81 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 288 (accept_3_5 80 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 79 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 288 (Polychromatic418967fa.accept_19_2_17_3_1_11224 78 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 288 (accept_3_5 77 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 76 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 75 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 288 (accept_3_5 74 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 288 (Polychromatic418967fa.accept_19_16_17_3_1_2916 73 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 288 (accept_3_5 71 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 288 (Polychromatic418967fa.accept_21_7_1_15_1_680 70 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 288
  (Polychromatic418967fa.accept_19_12_17_3_1_5515 69 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 169 288 (accept_3_5 68 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 169 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 288 (Polychromatic418967fa.accept_21_3_1_15_1_4287 66 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 288 (accept_3_5 65 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 64 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 169 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 63 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 288 (accept_3_5 62 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 288
  (Polychromatic418967fa.accept_21_18_1_15_1_11930 60 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 169 288 (accept_3_5 59 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 169 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 58 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 288 (accept_3_5 56 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 288
  (Polychromatic418967fa.accept_25_5_19_13_1_17803 55 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 288 (accept_3_5 53 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 51 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 288 (accept_3_5 50 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 49 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 288 (Polychromatic418967fa.accept_21_6_1_15_1_9016 48 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 288 (accept_3_5 47 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 46 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 288
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 45 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 288 (accept_3_5 44 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 288 (Polychromatic418967fa.accept_19_5_17_3_1_4152 43 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 288 (accept_3_5 41 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 288 (Polychromatic418967fa.accept_19_2_17_3_1_11224 40 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 288 (accept_3_5 38 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 288 (Polychromatic418967fa.accept_27_9_7_18_1_8251 36 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 288 (accept_3_5 35 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 288
  (Polychromatic418967fa.accept_19_14_17_3_1_4137 33 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 169 288 (accept_3_5 32 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 288 (accept_3_5 29 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 169 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 288 (accept_3_5 26 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 169 288 (Polychromatic418967fa.accept_19_6_17_3_1_11186 25 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 288 (accept_3_5 23 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 288 (accept_3_5 20 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 288 (Polychromatic418967fa.accept_20_19_9_8_1_12192 19 169
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 288
  (Polychromatic418967fa.accept_21_18_1_15_1_11930 18 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 169 288 (accept_3_5 17 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 169 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 169 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 288 (Polychromatic418967fa.accept_19_15_17_3_1_13760 15
  169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 288 (accept_3_5 14
  169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 288
  (Polychromatic418967fa.accept_22_13_15_2_1_17802 13 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 288 (Polychromatic418967fa.accept_19_12_17_3_1_5515 12 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 288 (accept_3_5 11 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 288 (Polychromatic418967fa.accept_21_10_1_15_1_10541 10
  169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 288 (accept_3_5 8 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 169 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 288 (accept_3_5 5 169 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 169 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 288
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 3 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 288 (accept_3_5 2 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 169 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 168 288 (Eq.refl Bool.true) (allA_succ_of_gcd 120 168 288 24 5 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 168 288
  (Polychromatic418967fa.accept_19_5_16_3_1_1820 119 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 168 288 2 59 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 117 168 288 3 39 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 168 288 4 29 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 168 288
  (Polychromatic418967fa.accept_19_1_16_3_1_11223 115 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 168 288 6 19 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 168 288 (Polychromatic418967fa.accept_17_11_15_16_1_4377 113 168 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 168 288 8 14 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 168 288 3 37 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 168 288 2 55 84
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 168 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 109 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 168 288 12 9 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 168 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 107 168 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 168 288 2 53 84 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 168 288 3 35 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 168 288 8 13 21
  36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 168 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 103 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 168 288 6 17 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 168 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 101 168 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 168 288 4 25 42 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 168 288 3 33 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 168 288 2 49 84
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 168 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 97 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 168 288 24 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 168 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 95 168 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 168 288 2 47 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 168 288 3 31 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 168 288 4 23 42 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 168 288
  (Polychromatic418967fa.accept_19_15_16_3_1_8409 91 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 168 288 6 15 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 168 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 89 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 288 8 11 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 168 288 3 29 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 168 288 2 43 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 168 288
  (Polychromatic418967fa.accept_22_19_14_2_1_3635 85 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 168 288 12 7 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 168 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 83 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 288 2 41 84 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 168 288 3 27 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 168 288 8 10 21 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 168 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 79 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 288 6 13 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 77 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 288 4 19 42 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 168 288 3 25 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 168 288 2 37 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 288
  (Polychromatic418967fa.accept_25_23_18_13_1_17801 73 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 168 288 24 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 168 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 288 2 35 84 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 168 288 3 23 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 168 288 4 17 42 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 288 6 11 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 288 (Polychromatic418967fa.accept_17_14_15_16_1_1271 65 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 288 8 8 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 168 288 3 21 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 288 2 31 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 288
  (Polychromatic418967fa.accept_19_4_16_3_1_4175 61 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 288 12 5 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 288 (Polychromatic418967fa.accept_19_2_16_3_1_7005 59 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 288 2 29 84 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 168 288 3 19 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 288 8 7 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 288
  (Polychromatic418967fa.accept_13_3_12_2_1_385 55 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 288 6 9 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 53 168 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 288 4 13 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 168 288 3 17 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 288 2 25 84 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 168 288 24 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 168 288 (Polychromatic418967fa.accept_22_3_14_2_1_13240 47 168 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 288 2 23 84 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 288 3 15 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 288 4 11 42
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 288 6 7 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 288 (Polychromatic418967fa.accept_22_19_14_2_1_3635 41 168 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 288 8 5 21 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 288 3 13 56 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 288 2 19 84 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 288
  (Polychromatic418967fa.accept_19_18_16_3_1_1803 37 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 288 12 3 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 288 (Polychromatic418967fa.accept_17_1_15_16_1_2202 35 168 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 288 2 17 84 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 288 3 11 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 288 8 4 21 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 288 6 5 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 168 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 168 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 288 4 7 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 288 3 9 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 288 2 13 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 288
  (Polychromatic418967fa.accept_19_6_16_3_1_1801 25 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 288 24 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 168 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 288 2 11 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 288 3 7 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 288 4 5 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707
  19 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 288 6 3 28 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 288 8 2 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 168 288 3 5 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 168 288 2 7 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 288 (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 288 12 1 14 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 288
  (Polychromatic418967fa.accept_17_11_15_16_1_4377 11 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 168 288 2 5 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 288 3 3 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 288 8 1 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 168 288 (Polychromatic418967fa.accept_25_7_18_13_1_17800 7 168 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 288 6 1 28 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 168 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 288 4 1 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 168 288 3 1 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 168 288 2 1 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 168 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 167 288 (Eq.refl Bool.true) (allA_succ_of_accept 121 167 288 (accept_3_4 121 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 167 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 120
  167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 167 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 119 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 167 288 (accept_3_4 118 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 167 288 (Polychromatic418967fa.accept_28_4_27_8_1_17678 116 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 167 288 (accept_3_4 115 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 114 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 167 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 113 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 167 288 (accept_3_4 112 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 167 288 (Polychromatic418967fa.accept_19_16_15_3_1_8408 111 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407
  110 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 167 288 (accept_3_4
  109 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 167 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 108 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 167 288 (accept_3_4 106 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 167 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 167 288
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 104 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 167 288 (accept_3_4 103 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 167 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 102 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 167 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 101 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 167 288 (accept_3_4 100 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 167 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 167 288 (Polychromatic418967fa.accept_21_14_20_15_1_4285 98
  167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 167 288 (accept_3_4 97
  167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 167 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 96 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 167 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 95 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 167 288 (accept_3_4 94 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 167 288
  (Polychromatic418967fa.accept_19_16_15_3_1_8408 92 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 167 288 (accept_3_4 91 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 167 288 (Polychromatic418967fa.accept_20_10_7_8_1_4923 90 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 167 288 (accept_3_4 88 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 167 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 87 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 288 (accept_3_4 85 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 167 288 (Polychromatic418967fa.accept_19_8_15_3_1_5546 84 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 288
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 83 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 167 288 (accept_3_4 82 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 167 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 81 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 80 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 288 (accept_3_4 79 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 288
  (Polychromatic418967fa.accept_25_3_17_13_1_16062 78 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 167 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 77 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 167 288 (accept_3_4 76 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 74 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 167 288 (accept_3_4 73 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 167 288 (Polychromatic418967fa.accept_22_5_13_2_1_17799 71 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 288 (accept_3_4 70 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 167 288 (accept_3_4 67 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 288 (Polychromatic418967fa.accept_17_15_14_16_1_5625 66 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 288 (accept_3_4 64 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 62 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 167 288 (accept_3_4 61 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 167 288 (Polychromatic418967fa.accept_21_18_20_15_1_8916 60 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  59 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 288 (accept_3_4 58
  167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 167 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 288 (accept_3_4 55 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 288
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 53 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 167 288 (accept_3_4 52 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 288 (accept_3_4 49 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 288 (accept_3_4 46 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 167 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 288 (accept_3_4 43 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 288 (Polychromatic418967fa.accept_20_1_7_8_1_4877 41 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 288 (accept_3_4 40 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 288
  (Polychromatic418967fa.accept_22_16_13_2_1_13228 38 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 167 288 (accept_3_4 37 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 167 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  35 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 288 (accept_3_4 34
  167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 167 288 (Polychromatic418967fa.accept_17_15_14_16_1_5625 32 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 288 (accept_3_4 31 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 288 (accept_3_4 28 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 288 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 288 (accept_3_4 25 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 288 (Polychromatic418967fa.accept_25_24_17_13_1_16046 24 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 288 (accept_3_4 22 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 288 (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 288 (accept_3_4 19 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 288 (Polychromatic418967fa.accept_19_18_15_3_1_5548 18 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 288 (accept_3_4 16 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 288 (accept_3_4 13 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 288
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 167 288 (accept_3_4 10 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 167 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 167 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 288 (Polychromatic418967fa.accept_17_8_14_16_1_6849 8 167
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 288 (accept_3_4 7 167 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 288
  (Polychromatic418967fa.accept_21_6_20_15_1_10532 6 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 288 (accept_3_4 4 167 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 167 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 288 (accept_3_4 1 167 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 166 288 (Eq.refl Bool.true) (allA_succ_of_gcd 122 166 288 2 61 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 166 288
  (Polychromatic418967fa.accept_19_7_14_3_1_1793 121 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 166 288 2 60 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 166 288 (accept_3_5 119 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 166 288 2 59 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 166 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 117 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 166 288 2 58 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 166 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 166 288 2 57 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 166 288 (accept_3_5 113 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 166 288 2 56 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 166 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 166 288 2 55 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 166 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 166 288 2 54 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 166 288 (accept_3_5 107 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 166 288 2 53 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 166 288 (Polychromatic418967fa.accept_17_3_13_16_1_2183 105 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 166 288 2 52 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 166 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 103 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 166 288 2 51 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 166 288 (accept_3_5 101 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 166 288 2 50 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 166 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 99 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 166 288 2 49 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 166 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 166 288 2 48 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 166 288 (accept_3_5 95 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 166 288 2 47 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 166 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 93 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 166 288 2 46 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 166 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 166 288 2 45 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 166 288 (accept_3_5 89 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 166 288 2 44 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 166 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 288 2 43 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 288
  (Polychromatic418967fa.accept_19_9_14_3_1_2912 85 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 166 288 2 42 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 166 288 (accept_3_5 83 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 288 2 41 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 288 2 40 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 79 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 288 2 39 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 288 (accept_3_5 77 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 288 2 38 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 288 (Polychromatic418967fa.accept_19_18_14_3_1_8427 75 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 288 2 37 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 288 2 36 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 288 (accept_3_5 71 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 288 2 35 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 288 2 34 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 288 2 33 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 288 (accept_3_5 65 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 288 2 32 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 288 2 31 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 288
  (Polychromatic418967fa.accept_25_11_16_13_1_2000 61 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 166 288 2 30 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 166 288 (accept_3_5 59 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 288 2 29 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 57 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 288 2 28 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 288 2 27 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 288 (accept_3_5 53 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 288 2 26 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 288 2 25 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 288
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 49 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 288 2 24 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 288 (accept_3_5 47 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 288 2 23 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 288 2 22 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 288 2 21 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 288 (accept_3_5 41 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 288 2 20 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 288 2 19 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 288
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 166 288 2 18 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 166 288 (accept_3_5 35 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 288 2 17 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 288 2 16 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 288 2 15 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 288 (accept_3_5 29 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 288 2 14 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 166 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 288 2 13 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 288 2 12 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 288 (accept_3_5 23 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 288 2 11 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 288 2 10 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 288 2 9 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 288 (accept_3_5 17 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 288 2 8 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 288 (Polychromatic418967fa.accept_26_15_10_2_1_10588 15 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 288 2 7 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 288 2 6 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 288 (accept_3_5 11 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 288 2 5 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 288 (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 288 2 4 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 288
  (Polychromatic418967fa.accept_19_7_14_3_1_1793 7 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 288 2 3 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 288 (accept_3_5 5 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  288 2 2 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 166 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 288 2 1 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 288 (Polychromatic418967fa.accept_21_1_19_15_1_8914 1 166 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 165 288 (Eq.refl Bool.true) (allA_succ_of_gcd 123 165 288 3 41 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 165 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 122 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 165 288 (Polychromatic418967fa.accept_19_7_13_3_1_4171 121 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 165 288 3 40 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 165 288
  (Polychromatic418967fa.accept_21_14_18_15_1_5756 119 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 165 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 118 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 165 288 3 39 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 165 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 116 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 115 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 165 288 3 38 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 165 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 113 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 165 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 112 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 111 165 288 3 37 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  110 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 165 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 109 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 165 288 3 36 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 165 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 107 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 288
  (Polychromatic418967fa.accept_19_11_13_3_1_9820 106 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 165 288 3 35 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 165 288 (Polychromatic418967fa.accept_19_9_13_3_1_9829 104 165 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 165 288 3 34 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 165 288
  (Polychromatic418967fa.accept_21_16_18_15_1_7282 100 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 165 288 3 33 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 165 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 98 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 97 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 165 288 3 32 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 165 288 (Polychromatic418967fa.accept_20_15_5_8_1_4920 95 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 165 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 94 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 165 288 3 31 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 165 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 92 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 288
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 91 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 165 288 3 30 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 88 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 165 288 3 29 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 165 288 (Polychromatic418967fa.accept_17_1_12_16_1_2211 86 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 85 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 165 288 3 28 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 165 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 82 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 165 288 3 27 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  79 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 165 288 3 26 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 165 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 165 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 76 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 165 288 3 25 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 165 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034
  74 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 165 288 3 24 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 165 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489
  70 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 165 288 3 23 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 165 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 165 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 288 3 22 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 288 (Polychromatic418967fa.accept_19_8_13_3_1_4172
  65 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 288
  (Polychromatic418967fa.accept_17_13_12_16_1_6908 64 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 165 288 3 21 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 165 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 288 3 20 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 288 (Polychromatic418967fa.accept_13_6_9_2_1_838
  58 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 288 3 19 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 288
  (Polychromatic418967fa.accept_21_14_18_15_1_5756 56 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 165 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 288 3 18 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 288 3 17 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 165 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969
  50 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 288
  (Polychromatic418967fa.accept_19_11_13_3_1_9820 49 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 165 288 3 16 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 46 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 288 3 15 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 288 3 14 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 288 (Polychromatic418967fa.accept_21_20_18_15_1_11881 41 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 165 288 3 13 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 165 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  37 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 288 3 12 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 288
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 35 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 165 288 (Polychromatic418967fa.accept_20_14_5_8_1_4870 34 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 288 3 11 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 288 3 10 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486
  29 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 288
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 28 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 165 288 3 9 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 288
  (Polychromatic418967fa.accept_22_3_11_2_1_17798 25 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 165 288 3 8 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 165 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 165 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 288 3 7 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 165 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 288 3 6 55 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 16 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 288 3 5 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  14 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 288 3 4 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 165 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 288 3 3 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 288
  (Polychromatic418967fa.accept_19_8_13_3_1_4172 8 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 288 3 2 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 165 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 165 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 288 3 1 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 165 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 165 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 164 288 (Eq.refl Bool.true) (allA_succ_of_gcd 124 164 288 4 31 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 164 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 123 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 164 288 2 61 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 164 288 (accept_3_4 121 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 164 288 4 30 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 164 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 119 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 164 288 2 59 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 164 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 117 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 164 288 4 29 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 164 288 (accept_3_4 115 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 164 288 2 57 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 164 288 (Polychromatic418967fa.accept_21_8_17_15_1_2834 113 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 164 288 4 28 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 164 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 111 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 164 288 2 55 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 164 288 (accept_3_4 109 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 164 288 4 27 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 164 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 164 288 2 53 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 164 288
  (Polychromatic418967fa.accept_19_10_12_3_1_12558 105 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 164 288 4 26 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 164 288 (accept_3_4 103 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 164 288 2 51 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 164 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 101 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 164 288 4 25 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 164 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 99 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 164 288 2 49 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 164 288 (accept_3_4 97 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 164 288 4 24 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 164 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 164 288 2 47 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 164 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 164 288 4 23 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 164 288 (accept_3_4 91 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 164 288 2 45 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 164 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 288 4 22 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 288
  (Polychromatic418967fa.accept_19_11_12_3_1_8407 87 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 164 288 2 43 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 164 288 (accept_3_4 85 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 288 4 21 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 288 (Polychromatic418967fa.accept_17_15_11_16_1_3263 83 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 288 2 41 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 288 4 20 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 288 (accept_3_4 79 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 288 2 39 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 77 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 288 4 19 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 288 2 37 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 288 (accept_3_4 73 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 288 4 18 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 288 2 35 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 288 4 17 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 288 (accept_3_4 67 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 288 2 33 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 288 4 16 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 288
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 63 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 164 288 2 31 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 164 288 (accept_3_4 61 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 288 4 15 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 288 2 29 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 288
  (Polychromatic418967fa.accept_22_13_10_2_1_5206 57 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 164 288 4 14 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 164 288 (accept_3_4 55 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 288 2 27 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 288 4 13 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 288 2 25 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 288 (accept_3_4 49 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 288 4 12 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 288 2 23 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 288 4 11 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 288 (accept_3_4 43 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 288 2 21 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 288 4 10 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 288 2 19 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 288 (accept_3_4 37 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 288 4 9 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 288 (Polychromatic418967fa.accept_21_14_17_15_1_9017 35 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 288 2 17 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 288 4 8 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 164 288 (accept_3_4 31 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  164 288 2 15 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 164 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 164 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 288 4 7 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 288
  (Polychromatic418967fa.accept_21_6_17_15_1_2833 27 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 164 288 2 13 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 164 288 (accept_3_4 25 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 288 4 6 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 164 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 164 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 288 2 11 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 288 (Polychromatic418967fa.accept_19_2_12_3_1_5446
  21 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 288 4 5 41 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 288
  (accept_3_4 19 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 288 2 9 82 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 288
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 164 288 4 4 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 164 288 (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 164 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 288 2 7 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 288 (accept_3_4 13 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 288 4 3 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 288 2 5 82 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 288 4 2 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 288 (accept_3_4 7 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  288 2 3 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 288 4 1 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 288 (Polychromatic418967fa.accept_21_3_17_15_1_4199 3 164 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 288 2 1 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 288 (accept_3_4 1 164 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 163 288 (Eq.refl Bool.true) (allA_succ_of_accept 125 163 288 (accept_3_5 125 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 163 288 (Polychromatic418967fa.accept_19_10_11_3_1_12543 124
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 163 288
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 123 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 163 288 (accept_3_5 122 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 121 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 163 288 (Polychromatic418967fa.accept_29_4_18_27_1_17797 120
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 163 288 (accept_3_5 119
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 163 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 118 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 163 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 117 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 163 288 (accept_3_5 116 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 115 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 163 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 114 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 163 288 (accept_3_5 113 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 163 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 112 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 111 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 163 288 (accept_3_5 110 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 163 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 109 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 163 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 108 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 163 288 (accept_3_5 107 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 163 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 106 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 163 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 105 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 163 288 (accept_3_5 104 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 163 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 103 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 163 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 102 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 163 288 (accept_3_5 101 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 163 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 100 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988
  99 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 163 288 (accept_3_5 98
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 163 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 163 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 96 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 288 (accept_3_5 95 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 288
  (Polychromatic418967fa.accept_20_13_3_8_1_4865 93 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 288 (accept_3_5 92 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 91 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 288 (accept_3_5 89 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 288 (Polychromatic418967fa.accept_19_12_11_3_1_8399 88 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 288 (accept_3_5 86 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 85 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 84 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 288 (accept_3_5 83 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 288 (Polychromatic418967fa.accept_22_16_9_2_1_11686 82 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 81 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 288 (accept_3_5 80 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 288 (Polychromatic418967fa.accept_23_10_2_12_1_11407 79 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 288 (Polychromatic418967fa.accept_19_2_11_3_1_4136 78 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 288 (accept_3_5 77 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  76 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 288 (accept_3_5 74 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 288 (accept_3_5 71 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 288 (accept_3_5 68 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 288 (Polychromatic418967fa.accept_19_10_11_3_1_12543 67 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 288 (accept_3_5 65 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 288 (Polychromatic418967fa.accept_21_1_16_15_1_8913 64 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 288
  (Polychromatic418967fa.accept_27_9_1_18_1_15985 63 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 163 288 (accept_3_5 62 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 288 (accept_3_5 59 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 288
  (Polychromatic418967fa.accept_17_7_10_16_1_5582 58 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 288 (accept_3_5 56 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 54 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 288 (accept_3_5 53 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 288 (accept_3_5 50 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 288 (Polychromatic418967fa.accept_27_22_1_18_1_17796 49
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 288 (accept_3_5 47 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 288 (accept_3_5 44 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 43 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 163 288 (accept_3_5 41 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 163 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 288 (accept_3_5 38 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 163 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 288 (accept_3_5 35 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 288
  (Polychromatic418967fa.accept_19_14_11_3_1_5508 33 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 163 288 (accept_3_5 32 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 288 (Polychromatic418967fa.accept_21_9_16_15_1_9014 30 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 288 (accept_3_5 29 163
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 288
  (Polychromatic418967fa.accept_19_9_11_3_1_5580 28 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 288 (accept_3_5 26 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 163 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 288 (accept_3_5 23 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 288 (accept_3_5 20 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 288 (Polychromatic418967fa.accept_27_19_1_18_1_17795 19
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 288 (accept_3_5 17 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 288 (accept_3_5 14 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 288
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 163 288 (accept_3_5 11 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 163 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 288 (accept_3_5 8 163 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7
  163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 288 (accept_3_5 5 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 163 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 288 (accept_3_5 2 163 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 163 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 162 288 (Eq.refl Bool.true) (allA_succ_of_gcd 126 162 288 18 7 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 162 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 125 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 162 288 2 62 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 162 288 3 41 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 162 288 2 61 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 162 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 121 162
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 162 288 6 20 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 162 288
  (Polychromatic418967fa.accept_19_5_10_3_1_5460 119 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 162 288 2 59 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 117 162 288 9 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 162 288 2 58 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 162 288 (Polychromatic418967fa.accept_10_5_2_8_1_135
  115 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 288 6 19 27 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 113 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 162 288 2 56 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 162 288 3 37 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 162 288 2 55 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 162 288 (Polychromatic418967fa.accept_22_21_8_2_1_16285 109
  162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 288 18 6 9 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 107 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 162 288 2 53 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 162 288 3 35 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 162 288 2 52 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 162 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 103 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 162 288 6 17 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 162 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 101 162 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 162 288 2 50 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 162 288 9 11 18 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 162 288 2 49 81
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 162 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 97 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 162 288 6 16 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 162 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 162 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 288 2 47 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 162 288 3 31 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 162 288 2 46 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 162 288
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 288 18 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 162 288 (Polychromatic418967fa.accept_19_13_10_3_1_11235 89 162 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 288 2 44 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 162 288 3 29 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 162 288 2 43 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 288 6 14 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 83 162 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 288 2 41 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 162 288 9 9 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 162 288 2 40 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 79 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 288 6 13 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 162 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 288 2 38 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 162 288 3 25 54 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 162 288 2 37 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 73 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 288 18 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 162 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 288 2 35 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 162 288 3 23 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 288 2 34 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 288 6 11 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 162 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 288 2 32 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 288 9 7 18 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 288 2 31 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 288 6 10 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 288 (Polychromatic418967fa.accept_17_8_9_16_1_6844 59 162 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 288 2 29 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 288 3 19 54 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 288 2 28 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 288 18 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 53 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 288 2 26 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 288 3 17 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 288 2 25 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 288 6 8 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 288 2 23 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 288 9 5 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 288 2 22 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 288 6 7 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 288 (Polychromatic418967fa.accept_28_13_22_8_1_17794 41 162 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 288 2 20 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 288 3 13 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 288 2 19 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 288 18 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 288 2 17 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 288 3 11 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 288 2 16 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 288
  (Polychromatic418967fa.accept_19_12_10_3_1_5503 31 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 288 6 5 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 288 (Polychromatic418967fa.accept_25_4_12_13_1_17793 29 162 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 288 2 14 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 288 9 3 18 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 288 2 13 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 288 6 4 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 288 2 11 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 288 3 7 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 288 2 10 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 288
  (Polychromatic418967fa.accept_29_19_17_27_1_17792 19 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 288 18 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 162 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 288 2 8 81 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 288 3 5 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 288 2 7 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 288 6 2 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 288 (Polychromatic418967fa.accept_19_11_10_3_1_2934 11 162 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 288 2 5 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 288 9 1 18 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 288 2 4 81 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 288 6 1 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 162 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 288 2 2 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 288 3 1 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 288 2 1 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 1
  162 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 161 288 (Eq.refl Bool.true) (allA_succ_of_accept 127 161 288 (accept_3_4 127 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 161 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 126 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 161 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 125 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 161 288 (accept_3_4 124 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 123 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 161 288 (Polychromatic418967fa.accept_21_17_14_15_1_5750 122 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 161 288 (accept_3_4 121 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 161 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 120 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 161 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 119 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 161 288 (accept_3_4 118 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 161 288 (Polychromatic418967fa.accept_21_12_14_15_1_8909 117 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 116 161 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 161 288 (accept_3_4 115 161 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 161 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 114 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 113 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 161 288 (accept_3_4 112 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 161 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 111 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 161 288
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 110 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 161 288 (accept_3_4 109 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 161 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 108 161 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 161 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 107 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 161 288 (accept_3_4 106 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 161 288 (Polychromatic418967fa.accept_19_10_9_3_1_7009 105 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 161 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 104 161 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 161 288 (accept_3_4 103 161 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 161 288
  (Polychromatic418967fa.accept_21_18_14_15_1_5809 102 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 161 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 101 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 288 (accept_3_4 100 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 99 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 98 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 288 (accept_3_4 97 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 96 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 95 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 288 (accept_3_4 94 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 93 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 288
  (Polychromatic418967fa.accept_17_7_8_16_1_6966 92 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 288 (accept_3_4 91 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 90 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 89 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 288 (accept_3_4 88 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 87 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 86 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 288 (accept_3_4 85 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 288 (Polychromatic418967fa.accept_22_18_7_2_1_10017 84 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 288 (accept_3_4 82 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 81 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 288
  (Polychromatic418967fa.accept_21_17_14_15_1_5750 80 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 161 288 (accept_3_4 79 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 161 288 (Polychromatic418967fa.accept_20_18_1_8_1_9326 78 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 288 (accept_3_4 76 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 161 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 74 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 288 (accept_3_4 73 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 161 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 71 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 161 288 (accept_3_4 70 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 161 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 288 (accept_3_4 67 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 66 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 288
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 65 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 161 288 (accept_3_4 64 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 62 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 288 (accept_3_4 61 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 288
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 60 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 59 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 288 (accept_3_4 58 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 161 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 57 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 56 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 288 (accept_3_4 55 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 288 (Polychromatic418967fa.accept_21_12_14_15_1_8909 54 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 288 (accept_3_4 52 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 288
  (Polychromatic418967fa.accept_19_12_9_3_1_13858 50 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 161 288 (accept_3_4 49 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 161 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 161 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 288 (Polychromatic418967fa.accept_20_7_1_8_1_10806 47 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 288 (accept_3_4 46 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 288
  (Polychromatic418967fa.accept_21_3_14_15_1_10526 45 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 288 (accept_3_4 43 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 288
  (Polychromatic418967fa.accept_14_13_7_8_1_677 41 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 288 (accept_3_4 40 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 38 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 288 (accept_3_4 37 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 288 (accept_3_4 34 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 288 (Polychromatic418967fa.accept_19_13_9_3_1_9806 32 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 288 (accept_3_4 31 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 288 (accept_3_4 28 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 288 (Polychromatic418967fa.accept_17_9_8_16_1_2176 26 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 288 (accept_3_4 25 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 288 (Polychromatic418967fa.accept_17_7_8_16_1_6966 24 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 288 (accept_3_4 22 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 288 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 288 (accept_3_4 19 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 288 (Polychromatic418967fa.accept_19_18_9_3_1_8430 18 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 288 (accept_3_4 16 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 288 (accept_3_4 13 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 161
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 288
  (Polychromatic418967fa.accept_19_11_9_3_1_4167 11 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 288 (accept_3_4 10 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 288 (accept_3_4 7 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 161 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 288
  (Polychromatic418967fa.accept_21_5_14_15_1_7290 5 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 288 (accept_3_4 4 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 161 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 288 (Polychromatic418967fa.accept_17_2_8_16_1_4403 2 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 288 (accept_3_4 1 161 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 161
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 160 288 (Eq.refl Bool.true) (allA_succ_of_gcd 128 160 288 32 4 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 160 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 127 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 160 288 2 63 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 160 288 (accept_3_5 125 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 160 288 4 31 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 160 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 123 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 160 288 2 61 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 160 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 121 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 160 288 8 15 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 160 288 (accept_3_5 119 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 160 288 2 59 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 160 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 117 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 160 288 4 29 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 160 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 115 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 160 288 2 57 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 160 288 (accept_3_5 113 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 160 288 16 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 160 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 111 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 160 288 2 55 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 160 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 109 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 160 288 4 27 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 160 288 (accept_3_5 107 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 160 288 2 53 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 160 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 105 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 160 288 8 13 20 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 160 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 160 288 2 51 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 160 288 (accept_3_5 101 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 160 288 4 25 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 160 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 99 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 160 288 2 49 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 160 288
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 97 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 160 288 32 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 160 288 (accept_3_5 95 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94
  160 288 2 47 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 93 160 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 160 288 4 23 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 160 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856
  91 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 160 288 2 45 80 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 160 288
  (accept_3_5 89 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 160 288 8 11 20 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 160 288
  (Polychromatic418967fa.accept_19_11_8_3_1_862 87 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 160 288 2 43 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 160 288 (Polychromatic418967fa.accept_22_19_6_2_1_16233 85 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 160 288 4 21 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 160 288 (accept_3_5 83 160 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 160 288 2 41 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 160 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 81 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 160 288 16 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 160 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 160 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 160 288 2 39 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 160 288 (accept_3_5 77 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 160 288 4 19 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 160 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 75
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 160 288 2 37 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 288
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 73 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 160 288 8 9 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 160 288 (accept_3_5 71 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 160 288 2 35 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 160 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 288 4 17 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 67 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 160 288 2 33 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 160 288 (accept_3_5 65 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 160 288 32 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 160 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 288 2 31 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 61
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 288 4 15 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 288 (accept_3_5 59
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 288 2 29 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 57 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 288 8 7 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 160 288 (Polychromatic418967fa.accept_19_17_8_3_1_11211 55 160 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 160 288 2 27 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 288 (accept_3_5 53 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 288 4 13 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 288 2 25 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 49 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 288 16 3 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 288 (accept_3_5 47 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 288 2 23 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 288 4 11 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 288
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 288 2 21 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 288 (accept_3_5 41 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 288 8 5 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 160 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 288 2 19 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 288 4 9 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 288 (accept_3_5 35
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 288 2 17 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 288 32 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 288 2 15 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 288 (accept_3_5 29 160 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 288 4 7 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 288 (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 160
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 288 2 13 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 288 8 3 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 160 288 (accept_3_5 23 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  160 288 2 11 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 160 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 288 4 5 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 288 2 9 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 288 (accept_3_5 17
  160 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 288 16 1 10 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 288
  (Polychromatic418967fa.accept_11_4_6_2_1_51 15 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 160 288 2 7 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 160 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 288 4 3 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 288 (accept_3_5 11 160 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 288 2 5 80 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 288 8 1 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 160 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 288 2 3 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 288 (accept_3_5 5 160 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 288 4 1 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 288 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 160 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 288 2 1 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 288
  (Polychromatic418967fa.accept_22_1_6_2_1_8444 1 160 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 159 288 (Eq.refl Bool.true) (allA_succ_of_gcd 129 159 288 3 43 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 159 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 128 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 127 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 159 288 3 42 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 125 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 159 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 124 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 159 288 3 41 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72
  122 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 159 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 121 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 159 288 3 40 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 159 288 (Polychromatic418967fa.accept_19_5_7_3_1_6990 119 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 118 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 159 288 3 39 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 116 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 115 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 159 288 3 38 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 159 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 113 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 159 288
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 112 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 159 288 3 37 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 159 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 110 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 109 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 159 288 3 36 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 107 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 159 288
  (Polychromatic418967fa.accept_21_1_12_15_1_2880 106 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 159 288 3 35 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 159 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 104 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 103 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 159 288 3 34 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 159 288
  (Polychromatic418967fa.accept_13_9_3_2_1_399 100 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 159 288 3 33 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 159 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 98 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 159 288 3 32 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 94
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 159 288 3 31 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 159 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 92 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 159 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 91 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 159 288 3 30 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 159 288 (Polychromatic418967fa.accept_13_11_3_2_1_863
  89 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 88 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 159 288 3 29 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 159 288 (Polychromatic418967fa.accept_19_10_7_3_1_6977 86 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 159 288 3 28 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 159 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 288 (Polychromatic418967fa.accept_19_6_7_3_1_1733
  82 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 159 288 3 27 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 159 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 159 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 159 288 3 26 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  77 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 76 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 288 3 25 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 74 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 73
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 159 288 3 24 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 159 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 70 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 288 3 23 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194
  68 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 159 288 3 22 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 159 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 288 (Polychromatic418967fa.accept_10_4_9_8_1_125
  64 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 288 3 21 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 288 3 20 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 288 3 19 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 288 (Polychromatic418967fa.accept_21_14_12_15_1_7299 56 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 288 3 18 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 288 3 17 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 50 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 288 3 16 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135
  47 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 46 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 288 3 15 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 288 3 14 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  40 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 288 3 13 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 288 3 12 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 288 (Polychromatic418967fa.accept_13_9_3_2_1_399
  35 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 288 3 11 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 159 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 288 3 10 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 288
  (Polychromatic418967fa.accept_19_10_7_3_1_6977 29 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 288 3 9 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280
  26 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 288 3 8 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 159
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 288 3 7 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 288 3 6 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 288
  (Polychromatic418967fa.accept_26_16_3_2_1_17791 16 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 159 288 3 5 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 159 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 159 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 288 3 4 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 159 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 288 3 3 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 288 3 2 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 159 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 159 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 288 3 1 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 288 (Polychromatic418967fa.accept_23_2_21_12_1_9772 2 159 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 159 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 158 288 (Eq.refl Bool.true) (allA_succ_of_gcd 130 158 288 2 65 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 158 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 129 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 158 288 2 64 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 158 288 (accept_3_4 127 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 158 288 2 63 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 158 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 125 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 158 288 2 62 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 158 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 123 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 158 288 2 61 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 158 288 (accept_3_4 121 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 158 288 2 60 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 158 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 119 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 158 288 2 59 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 158 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 117 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 158 288 2 58 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 158 288 (accept_3_4 115 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 158 288 2 57 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 158 288 (Polychromatic418967fa.accept_17_11_5_16_1_5600 113 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 158 288 2 56 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 158 288
  (Polychromatic418967fa.accept_19_16_6_3_1_6972 111 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 158 288 2 55 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 158 288 (accept_3_4 109 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 158 288 2 54 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 158 288 (Polychromatic418967fa.accept_23_15_20_12_1_17790 107 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 158 288 2 53 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 158 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 105 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 158 288 2 52 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 158 288 (accept_3_4 103 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 158 288 2 51 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 158 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 158 288 2 50 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 158 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 99 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 158 288 2 49 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 158 288 (accept_3_4 97 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 158 288 2 48 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 158 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 95 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 288 2 47 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 288
  (Polychromatic418967fa.accept_19_17_6_3_1_9830 93 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 288 2 46 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 288 (accept_3_4 91 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 288 2 45 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 288 2 44 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 87 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 288 2 43 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 288 (accept_3_4 85 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 288 2 42 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 83 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 288 2 41 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 81 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 288 2 40 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 288 (accept_3_4 79 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 288 2 39 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 288 (Polychromatic418967fa.accept_19_1_6_3_1_6968 77 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 288 2 38 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 288 2 37 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 288 (accept_3_4 73 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 288 2 36 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 71 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 288 2 35 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 69 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 288 2 34 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 288 (accept_3_4 67 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 288 2 33 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 65 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 288 2 32 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 288
  (Polychromatic418967fa.accept_20_3_18_8_1_4859 63 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 288 2 31 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 288 (accept_3_4 61 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 288 2 30 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 288 2 29 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 57 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 288 2 28 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 288 (accept_3_4 55 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 288 2 27 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 288 2 26 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 288
  (Polychromatic418967fa.accept_20_11_18_8_1_4821 51 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 158 288 2 25 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 158 288 (accept_3_4 49 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 288 2 24 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 288 2 23 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 288 2 22 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 288 (accept_3_4 43 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 288 2 21 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 288 (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 288 2 20 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 288 2 19 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 288 (accept_3_4 37 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 288 2 18 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 35 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 288 2 17 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 288 2 16 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 288 (accept_3_4 31 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 288 2 15 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 288 (Polychromatic418967fa.accept_27_2_23_18_1_17719 29 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 288 2 14 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 288 2 13 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 288 (accept_3_4 25 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 288 2 12 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 288 (Polychromatic418967fa.accept_19_4_6_3_1_15078 23 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 288 2 11 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 288
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 21 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 288 2 10 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 288 (accept_3_4 19 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 288 2 9 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 158 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 288 2 8 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 288
  (Polychromatic418967fa.accept_23_15_20_12_1_17790 15 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 158 288 2 7 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 158 288 (accept_3_4 13 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 288 2 6 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 288 2 5 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 288 2 4 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 288 (accept_3_4 7 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  288 2 3 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 158 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 288 2 2 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 158 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 288 2 1 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 288 (accept_3_4 1 158 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 157 288 (Eq.refl Bool.true) (allA_succ_of_accept 131 157 288 (accept_3_5 131 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 130 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 157 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 129 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 157 288 (accept_3_5 128 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 157 288 (Polychromatic418967fa.accept_20_7_17_8_1_3452 127 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 157 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 126 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 157 288 (accept_3_5 125 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424
  124 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 157 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 123 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 157 288 (accept_3_5 122 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 121 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 157 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 120 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 157 288 (accept_3_5 119 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 157 288 (Polychromatic418967fa.accept_23_3_19_12_1_17789 118
  157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 117 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 157 288 (accept_3_5 116 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 157 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 115 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 114 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 288 (accept_3_5 113 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 157 288 (Polychromatic418967fa.accept_19_17_5_3_1_5455 112
  157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 157 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 111 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 157 288 (accept_3_5 110 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 157 288 (Polychromatic418967fa.accept_21_3_10_15_1_4266 108 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 157 288 (accept_3_5 107 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 157 288 (Polychromatic418967fa.accept_21_1_10_15_1_2828 106
  157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 157 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 157 288 (accept_3_5 104 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 157 288 (accept_3_5 101 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 157 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 99 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 157 288 (accept_3_5 98 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 157 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 97 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 157 288 (accept_3_5 95 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 157 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 94 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 157 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 157 288 (accept_3_5 92 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 157 288 (Polychromatic418967fa.accept_20_11_17_8_1_4903 91 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 157 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 90 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 288 (accept_3_5 89 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 157 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 87 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 157 288 (accept_3_5 86 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 157 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 157 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 84 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 157 288 (accept_3_5 83 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 157 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 157 288 (accept_3_5 80 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 157 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 78 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 288 (accept_3_5 77 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 157 288 (Polychromatic418967fa.accept_22_10_3_2_1_13222 76 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 157 288 (accept_3_5 74 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 157 288 (Polychromatic418967fa.accept_17_5_4_16_1_6925 73 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 288 (accept_3_5 71 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 70 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 288 (accept_3_5 68 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 288 (Polychromatic418967fa.accept_17_15_4_16_1_6890 66 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 288 (accept_3_5 65 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 64 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 288
  (Polychromatic418967fa.accept_19_6_5_3_1_11210 63 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 288 (accept_3_5 62 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 288 (accept_3_5 59 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 288
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 288 (accept_3_5 56 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 55 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 288 (accept_3_5 53 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 288 (Polychromatic418967fa.accept_19_14_5_3_1_859 52 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 288 (accept_3_5 50 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 288 (accept_3_5 47 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 288 (accept_3_5 44 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 288 (Polychromatic418967fa.accept_21_1_10_15_1_2828 43 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 288 (accept_3_5 41 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 288 (accept_3_5 38 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 288 (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 288 (accept_3_5 35 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 288 (accept_3_5 32 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 288 (Polychromatic418967fa.accept_20_11_17_8_1_4903 31 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 288 (accept_3_5 29 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 288 (Polychromatic418967fa.accept_21_7_10_15_1_8906 28 157 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 288
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 288 (accept_3_5 26 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 288 (Polychromatic418967fa.accept_21_3_10_15_1_4266 24 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 288 (accept_3_5 23 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 288
  (Polychromatic418967fa.accept_19_2_5_3_1_5536 21 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 288 (accept_3_5 20 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 288 (accept_3_5 17 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 288 (accept_3_5 14 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 288 (Polychromatic418967fa.accept_27_13_22_18_1_6230 13 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 288 (accept_3_5 11 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 157
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 288 (accept_3_5 8 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 288 (Polychromatic418967fa.accept_19_7_5_3_1_13861 7 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 288 (accept_3_5 5 157 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 288 (accept_3_5 2 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 288 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 157 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 156 288 (Eq.refl Bool.true) (allA_succ_of_gcd 132 156 288 12 11 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 156 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 131 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 130 156 288 2 65 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 129 156 288 3 43 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 128 156 288 4 32 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 156 288 (Polychromatic418967fa.accept_14_1_2_8_1_655
  127 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 156 288 6 21 26 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 156 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 125 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 156 288 4 31 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 156 288 3 41 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 156 288 2 61 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 156 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 121 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 156 288 12 10 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 156 288
  (Polychromatic418967fa.accept_21_14_9_15_1_13409 119 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 156 288 2 59 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 117 156 288 3 39 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 156 288 4 29 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 156 288 (Polychromatic418967fa.accept_7_3_2_1_1_225
  115 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 288 6 19 26 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 113 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 156 288 4 28 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 156 288 3 37 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 156 288 2 55 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 156 288 (Polychromatic418967fa.accept_17_7_3_16_1_2208 109 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 156 288 12 9 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 156 288
  (Polychromatic418967fa.accept_21_2_9_15_1_5747 107 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 156 288 2 53 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 156 288 3 35 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 156 288 4 26 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 156 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  103 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 156 288 6 17 26 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 156 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 156 288 4 25 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 156 288 3 33 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 156 288 2 49 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 156 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 156 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 156 288 12 8 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 156 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 95 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 156 288 2 47 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 156 288 3 31 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 156 288 4 23 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 156 288 6 15 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 288
  (Polychromatic418967fa.accept_17_4_3_16_1_9483 89 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 156 288 4 22 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 156 288 3 29 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 156 288 2 43 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 85 156 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 156 288 12 7 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 156 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 288 2 41 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 156 288 3 27 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 156 288 4 20 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 288 (Polychromatic418967fa.accept_21_16_9_15_1_4265 79 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 156 288 6 13 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 156 288
  (Polychromatic418967fa.accept_19_1_4_3_1_8404 77 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 288 4 19 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 156 288 3 25 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 288 2 37 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 156 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 288 12 6 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 71 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 288 2 35 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 156 288 3 23 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 288 4 17 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 288 (Polychromatic418967fa.accept_21_4_9_15_1_11925 67 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 288 6 11 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 65 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 288 4 16 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 156 288 3 21 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 288 2 31 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 288 12 5 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 288 2 29 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 156 288 3 19 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 288 4 14 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 156 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 288 6 9 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 288 4 13 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 156 288 3 17 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 288 2 25 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 288 (Polychromatic418967fa.accept_19_11_4_3_1_5534 49 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 288 12 4 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 288
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 47 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 156 288 2 23 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 288 3 15 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 288 4 11 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  43 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 156 288 6 7 26 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 156 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 288 4 10 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 156 288 3 13 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 288 2 19 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 288 (Polychromatic418967fa.accept_19_18_4_3_1_4140 37 156
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 288 12 3 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 35 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 288 2 17 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 156 288 3 11 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 288 4 8 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 156 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 156 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 288 6 5 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 29 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 288 4 7 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 156 288 3 9 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 156 288 2 13 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 156 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 288 12 2 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 288 2 11 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 156 288 3 7 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 156 288 4 5 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 288 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 156 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 288 6 3 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 288 4 4 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 156 288 3 5 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 156 288 2 7 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 156 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 288 12 1 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 288 2 5 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 156 288 3 3 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 156 288 4 2 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 156 288 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 156 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 288 6 1 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 5
  156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 288 4 1 39 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 288 3 1 52 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 288 2 1 78 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 1 156 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 155 288 (Eq.refl Bool.true) (allA_succ_of_accept 133 155 288 (accept_3_4 133 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 132 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 155 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 131 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 155 288 (accept_3_4 130 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 155 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 129 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 155 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 128 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 155 288 (accept_3_4 127 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 155 288
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 126 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 155 288 (Polychromatic418967fa.accept_20_5_15_8_1_4930 125 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 155 288 (accept_3_4 124 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 123 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 155 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 122 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 155 288 (accept_3_4 121 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 155 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 120 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 119 155 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 119 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 155 288 (accept_3_4 118 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 155 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 117 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 155 288 (Polychromatic418967fa.accept_17_14_2_16_1_4380 116 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 288 (accept_3_4 115 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 114 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 155 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 113 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 155 288 (accept_3_4 112 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 155 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 111 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 155 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 110 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 155 288 (accept_3_4 109 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 155 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 108
  155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 107 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 155 288 (accept_3_4 106 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 155 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 105 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 155 288 (Polychromatic418967fa.accept_27_23_20_18_1_8273 104 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 288 (accept_3_4 103 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 102 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 101 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 155 288 (accept_3_4 100 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 155 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 99 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 155 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 288 (accept_3_4 97 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 96 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 155 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 95 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 155 288 (accept_3_4 94 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 93 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 155 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 92 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 155 288 (accept_3_4 91 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 155 288 (Polychromatic418967fa.accept_17_5_2_16_1_1294 90 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 155 288 (Polychromatic418967fa.accept_21_5_8_15_1_11890 89 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 288 (accept_3_4 88 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 155 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 86 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 155 288 (accept_3_4 85 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 155 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 83 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 288 (accept_3_4 82 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 81 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 288 (accept_3_4 79 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 288 (Polychromatic418967fa.accept_22_12_1_2_1_13238 78 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 288 (accept_3_4 76 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 75 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 288
  (Polychromatic418967fa.accept_20_14_15_8_1_9380 74 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 155 288 (accept_3_4 73 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 71 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 288 (accept_3_4 70 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 155 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 68 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 288 (accept_3_4 67 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 155 288 (Polychromatic418967fa.accept_13_1_12_2_1_384 66 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 288 (accept_3_4 64 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 288 (accept_3_4 61 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 288 (Polychromatic418967fa.accept_21_18_8_15_1_5745 60 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 288
  (Polychromatic418967fa.accept_17_8_2_16_1_5598 59 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 288 (accept_3_4 58 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 288 (accept_3_4 55 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 288 (accept_3_4 52 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 288 (Polychromatic418967fa.accept_20_10_15_8_1_4818 50 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 288 (accept_3_4 49 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 288 (Polychromatic418967fa.accept_17_14_2_16_1_4380 48 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 288 (accept_3_4 46 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 288 (accept_3_4 43 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 288
  (Polychromatic418967fa.accept_23_18_17_12_1_6323 41 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 155 288 (accept_3_4 40 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 155 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 288 (accept_3_4 37 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 155 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 35 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 288 (accept_3_4 34 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 288 (accept_3_4 31 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 288 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 288 (accept_3_4 28 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 288
  (Polychromatic418967fa.accept_21_5_8_15_1_11890 26 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 155 288 (accept_3_4 25 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 155 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 288 (accept_3_4 22 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 155 288 (Polychromatic418967fa.accept_23_20_17_12_1_17788 20 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 288 (accept_3_4 19 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 288 (accept_3_4 16 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 288 (Polychromatic418967fa.accept_22_15_1_2_1_17787 15 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 288 (accept_3_4 13 155 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 155
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 288
  (Polychromatic418967fa.accept_25_11_5_13_1_17725 11 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 288 (accept_3_4 10 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 155 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 288 (accept_3_4 7 155 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707
  6 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 288 (accept_3_4 4 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 155 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 288 (accept_3_4 1 155 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 154 288 (Eq.refl Bool.true) (allA_succ_of_gcd 134 154 288 2 67 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 154 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 133 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 132 154 288 2 66 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 131 154 288 (accept_3_5 131 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 154 288 2 65 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 154 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 129 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 154 288 2 64 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 154 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 127 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 154 288 2 63 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 154 288 (accept_3_5 125 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 154 288 2 62 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 154 288 (Polychromatic418967fa.accept_20_3_14_8_1_12152 123 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 154 288 2 61 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 154 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 121 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 154 288 2 60 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 154 288 (accept_3_5 119 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 154 288 2 59 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 154 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 117 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 154 288 2 58 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 154 288
  (Polychromatic418967fa.accept_19_1_2_3_1_6995 115 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 154 288 2 57 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 154 288 (accept_3_5 113 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 154 288 2 56 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 154 288 (Polychromatic418967fa.accept_19_16_2_3_1_5479 111 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 154 288 2 55 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 154 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 109 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 154 288 2 54 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 154 288 (accept_3_5 107 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 154 288 2 53 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 154 288 (Polychromatic418967fa.accept_20_5_14_8_1_6391 105 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 154 288 2 52 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 154 288
  (Polychromatic418967fa.accept_20_3_14_8_1_12152 103 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 154 288 2 51 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 154 288 (accept_3_5 101 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 154 288 2 50 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 154 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 99 154 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 154 288 2 49 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 97 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 154 288 2 48 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 154 288 (accept_3_5 95 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 154 288 2 47 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 154 288 (Polychromatic418967fa.accept_19_17_2_3_1_4190 93 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 154 288 2 46 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 154 288
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 91 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 154 288 2 45 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 154 288 (accept_3_5 89 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 288 2 44 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 87 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 288 2 43 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 288
  (Polychromatic418967fa.accept_20_5_14_8_1_6391 85 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 288 2 42 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 288 (accept_3_5 83 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 288 2 41 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 81 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 288 2 40 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 288 2 39 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 154 288 (accept_3_5 77 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 288 2 38 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 75 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 288 2 37 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 288
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 73 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 288 2 36 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 288 (accept_3_5 71 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 288 2 35 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 69 154 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 288 2 34 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 67 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 288 2 33 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 288 (accept_3_5 65 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 288 2 32 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 288 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 288 2 31 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 61 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 288 2 30 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 288 (accept_3_5 59 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 288 2 29 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 288 (Polychromatic418967fa.accept_27_3_19_18_1_17786 57 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 288 2 28 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 288 2 27 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 288 (accept_3_5 53 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 288 2 26 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 288 (Polychromatic418967fa.accept_21_9_7_15_1_5769 51 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 288 2 25 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 288 2 24 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 288 (accept_3_5 47 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 288 2 23 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 288 (Polychromatic418967fa.accept_20_5_14_8_1_6391 45 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 288 2 22 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 288 2 21 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 288 (accept_3_5 41 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 288 2 20 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 154 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 288 2 19 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 288 2 18 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 288 (accept_3_5 35 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 288 2 17 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 288 (Polychromatic418967fa.accept_20_13_14_8_1_4850 33 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 288 2 16 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 288
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 31 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 288 2 15 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 288 (accept_3_5 29 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 288 2 14 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 288 (Polychromatic418967fa.accept_23_4_16_12_1_17701 27 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 288 2 13 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 288
  (Polychromatic418967fa.accept_19_6_2_3_1_11217 25 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 288 2 12 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 288 (accept_3_5 23 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 288 2 11 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 288 (Polychromatic418967fa.accept_27_21_19_18_1_17785 21 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 288 2 10 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 288 2 9 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 288 (accept_3_5 17 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 288 2 8 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 288 (Polychromatic418967fa.accept_17_15_1_16_1_8166 15 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 288 2 7 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 288
  (Polychromatic418967fa.accept_20_13_14_8_1_4850 13 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 154 288 2 6 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 154 288 (accept_3_5 11 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 288 2 5 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 154 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 288 2 4 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 288
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 288 2 3 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 288 (accept_3_5 5 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  288 2 2 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 154 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 288 2 1 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 154 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 153 288 (Eq.refl Bool.true) (allA_succ_of_gcd 135 153 288 9 15 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 153 288
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 134 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 153 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 133 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 153 288 3 44 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 153 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 131 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 153 288 (Polychromatic418967fa.accept_19_16_1_3_1_7007 130 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 129 153 288 3 43 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 128 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 153 288 (Polychromatic418967fa.accept_21_1_6_15_1_5742 127 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 153 288 9 14 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 153 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 125 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 124 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 153 288 3 41 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 153 288 (Polychromatic418967fa.accept_11_1_10_2_1_58
  122 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 121 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 153 288 3 40 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 153 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 119 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 153 288
  (Polychromatic418967fa.accept_19_4_1_3_1_15091 118 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 117 153 288 9 13 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 116 153 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 116 153 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 115 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 153 288 3 38 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 153 288 (Polychromatic418967fa.accept_21_8_6_15_1_5743 113 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 112 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 153 288 3 37 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 110 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 109 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 153 288 9 12 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 153 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 106 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 153 288 3 35 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 153 288 (Polychromatic418967fa.accept_21_20_6_15_1_11937 104 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 103 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 153 288 3 34 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 153 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 101 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 100 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 153 288 9 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 153 288 (Polychromatic418967fa.accept_20_18_13_8_1_9398 98 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 97 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 153 288 3 32 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 153 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 95 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 94 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 153 288 3 31 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 153 288 (Polychromatic418967fa.accept_19_16_1_3_1_7007 92 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 91 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 153 288 9 10 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 288
  (Polychromatic418967fa.accept_21_4_6_15_1_5744 88 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 153 288 3 29 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 153 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  85 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 153 288 3 28 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 153 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 83 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 153 288 9 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 153 288 (Polychromatic418967fa.accept_19_4_1_3_1_15091
  80 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 288 3 26 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 153 288 3 25 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 153 288 (Polychromatic418967fa.accept_19_17_1_3_1_4160 74 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 288
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 73 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 153 288 9 8 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 153 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 288 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 153
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 153 288 3 23 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 153 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 288 3 22 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65
  153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 64 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 153 288 9 7 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 153 288 (Polychromatic418967fa.accept_19_5_1_3_1_8421 62 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 288 3 20 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216 59 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 58 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 288 3 19 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 288 9 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 153 288 (Polychromatic418967fa.accept_21_11_6_15_1_5764 53 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 288
  (Polychromatic418967fa.accept_21_10_6_15_1_8929 52 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 153 288 3 17 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 153 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 153 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 288
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 49 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 288 3 16 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  46 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 288 9 5 17 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 288 (Polychromatic418967fa.accept_19_5_1_3_1_8421 43 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 288 3 14 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  41 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 288 3 13 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 153 288 9 4 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 153 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 153
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 288 3 11 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 288
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 288 3 10 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 288 (Polychromatic418967fa.accept_13_3_10_2_1_381
  29 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 288
  (Polychromatic418967fa.accept_29_28_8_27_1_17784 28 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 153 288 9 3 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 288 3 8 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 288 (Polychromatic418967fa.accept_21_1_6_15_1_5742 22 153
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 288 3 7 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 288
  (Polychromatic418967fa.accept_21_20_6_15_1_11937 20 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 288 9 2 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 288
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 288 3 5 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 288
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 14 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 288 (Polychromatic418967fa.accept_21_13_6_15_1_5818 13 153 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 288 3 4 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 288 (Polychromatic418967fa.accept_19_10_1_3_1_12548 10 153 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 288 9 1 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450
  8 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 288
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 288 3 2 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 288 (Polychromatic418967fa.accept_19_4_1_3_1_15091 4 153
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 288 3 1 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 153 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 153 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 152 288 (Eq.refl Bool.true) (allA_succ_of_gcd 136 152 288 8 17 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 135 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 152 288 2 67 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 152 288 (accept_3_4 133 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 152 288 4 33 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 152 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 131 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 152 288 2 65 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 152 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 129 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 152 288 8 16 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 152 288 (accept_3_4 127 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 152 288 2 63 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 152 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 125 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 152 288 4 31 38 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 152 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 123 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 152 288 2 61 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 152 288 (accept_3_4 121 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 152 288 8 15 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 152 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 119 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 152 288 2 59 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 152 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 117 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 152 288 4 29 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 152 288 (accept_3_4 115 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 152 288 2 57 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 152 288 (Polychromatic418967fa.accept_21_8_5_15_1_4208 113 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 152 288 8 14 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 152 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 111 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 152 288 2 55 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 152 288 (accept_3_4 109 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 152 288 4 27 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 152 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 107 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 152 288 2 53 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 105 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 152 288 8 13 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 152 288 (accept_3_4 103 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 152 288 2 51 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 152 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 152 288 4 25 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 288
  (Polychromatic418967fa.accept_22_11_20_2_1_3577 99 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 152 288 2 49 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 152 288 (accept_3_4 97 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 152 288 8 12 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 152 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 152 288 2 47 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 152 288
  (Polychromatic418967fa.accept_21_9_5_15_1_5741 93 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 152 288 4 23 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 152 288 (accept_3_4 91 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 152 288 2 45 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 152 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 89 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 288 8 11 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 288 2 43 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 288 (accept_3_4 85 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 288 4 21 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 288 2 41 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 288 8 10 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 288 (accept_3_4 79 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 288 2 39 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 288 (Polychromatic418967fa.accept_21_14_5_15_1_11932 77 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 288 4 19 38 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 288 2 37 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 288 (accept_3_4 73 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 288 8 9 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 152 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 288 2 35 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 69
  152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 152 288 4 17 38 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 152 288 (accept_3_4 67
  152 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 152 288 2 33 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 65 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 152 288 8 8 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 152 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 152 288 2 31 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 152 288 (accept_3_4 61 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 152 288 4 15 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 152 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 152 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 288 2 29 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 288
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 57 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 288 8 7 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 152 288 (accept_3_4 55 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  152 288 2 27 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 152 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 288 4 13 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 288 (Polychromatic418967fa.accept_11_7_9_2_1_260
  51 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 152 288 2 25 76 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 152 288
  (accept_3_4 49 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 152 288 8 6 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 152 288
  (Polychromatic418967fa.accept_22_3_20_2_1_5223 47 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 152 288 2 23 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 152 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 152 288 4 11 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 152 288 (accept_3_4 43 152 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 152 288 2 21 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 288 8 5 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 288 2 19 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 288 (accept_3_4 37 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 288 4 9 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 288 2 17 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167
  33 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 288 8 4 19 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 288
  (accept_3_4 31 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 288 2 15 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 288 4 7 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 288 2 13 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 288 (accept_3_4 25 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 288 8 3 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 288 (Polychromatic418967fa.accept_25_23_2_13_1_17783 23 152
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 288 2 11 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 288
  (Polychromatic418967fa.accept_23_21_14_12_1_14580 21 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 152 288 4 5 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 152 288 (accept_3_4 19 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 288 2 9 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 288 8 2 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 288 2 7 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 288 (accept_3_4 13 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 288 4 3 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 152 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 288 2 5 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 288 (Polychromatic418967fa.accept_21_9_5_15_1_5741
  9 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 288 8 1 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 288 (accept_3_4 7
  152 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 288 2 3 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 152 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 152 288 4 1 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 152 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 288 2 1 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 288 (accept_3_4 1 152 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 151 288 (Eq.refl Bool.true) (allA_succ_of_accept 137 151 288 (accept_3_5 137 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 136 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 151 288
  (Polychromatic418967fa.accept_19_2_18_3_1_5517 135 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 151 288 (accept_3_5 134 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 133 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 151 288 (Polychromatic418967fa.accept_21_6_4_15_1_9005 132
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 151 288 (accept_3_5 131
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 151 288
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 130 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 129 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 151 288 (accept_3_5 128 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 151 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 127
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 151 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 126 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 151 288 (accept_3_5 125 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 124 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 123 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 151 288 (accept_3_5 122 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 151 288 (Polychromatic418967fa.accept_20_1_11_8_1_7894 121
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 151 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 120 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 151 288 (accept_3_5 119 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 151 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 118 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412
  117 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 151 288 (accept_3_5
  116 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 151 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 151 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 114 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 288 (accept_3_5 113 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 288 (Polychromatic418967fa.accept_25_12_1_13_1_17782 112 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 111 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 288 (accept_3_5 110 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 109 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 288 (accept_3_5 107 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 288 (Polychromatic418967fa.accept_17_4_15_16_1_3231 106
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 151 288
  (Polychromatic418967fa.accept_22_17_19_2_1_2229 105 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 151 288 (accept_3_5 104 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 103 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 151 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 102
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 288 (accept_3_5 101
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 288
  (Polychromatic418967fa.accept_22_12_19_2_1_11680 100 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 99 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 151 288 (accept_3_5 98 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 151 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 97 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 151 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 96 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 151 288 (accept_3_5 95 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 93 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 151 288 (accept_3_5 92 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 151 288 (Polychromatic418967fa.accept_19_15_18_3_1_1807 91 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 151 288
  (Polychromatic418967fa.accept_19_14_18_3_1_12569 90 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 151 288 (accept_3_5 89 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 151 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 88 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 288 (accept_3_5 86 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483
  85 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 288
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 151 288 (accept_3_5 83 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 151 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 81 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 288 (accept_3_5 80 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 288
  (Polychromatic418967fa.accept_19_2_18_3_1_5517 78 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 288 (accept_3_5 77 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 288 (Polychromatic418967fa.accept_27_22_16_18_1_17781 76 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 288 (accept_3_5 74 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 288 (accept_3_5 71 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 288 (Polychromatic418967fa.accept_23_1_13_12_1_3002 70 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 288 (accept_3_5 68 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 288 (Polychromatic418967fa.accept_25_17_1_13_1_17780 67
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 288 (accept_3_5 65 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 64 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 288 (accept_3_5 62 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 288
  (Polychromatic418967fa.accept_11_5_8_2_1_588 60 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 288 (accept_3_5 59 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 58 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 57 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 288 (accept_3_5 56 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 288 (Polychromatic418967fa.accept_17_4_15_16_1_3231 55 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 288 (accept_3_5 53 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 51 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 288 (accept_3_5 50 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 288
  (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 151 288 (accept_3_5 47 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 151 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 288 (accept_3_5 44 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  43 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 288
  (Polychromatic418967fa.accept_19_4_18_3_1_5553 42 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 288 (accept_3_5 41 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 288 (accept_3_5 38 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 37 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 288
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 288 (accept_3_5 35 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 288 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 288 (accept_3_5 32 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 288
  (Polychromatic418967fa.accept_19_11_18_3_1_1755 30 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 151 288 (accept_3_5 29 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 151 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 288 (accept_3_5 26 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 288
  (Polychromatic418967fa.accept_19_6_18_3_1_11230 25 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 288 (accept_3_5 23 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 288 (Polychromatic418967fa.accept_23_22_13_12_1_6297 22 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 288
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 288 (accept_3_5 20 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 288 (accept_3_5 17 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 151
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 288
  (Polychromatic418967fa.accept_19_15_18_3_1_1807 15 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 151 288 (accept_3_5 14 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 151 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 151 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 288 (accept_3_5 11 151 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 288 (accept_3_5 8 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 288 (accept_3_5 5 151 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 151 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 288 (accept_3_5 2 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 288 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 151 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 139 150 288 (Eq.refl Bool.true) (allA_succ_of_gcd 138 150 288 6 23 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 150 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 137 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 150 288 2 68 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 135 150 288 3 45 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 134 150 288 2 67 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 150 288 (Polychromatic418967fa.accept_21_7_3_15_1_5800 133 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 150 288 6 22 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 150 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 131 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 150 288 2 65 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 129 150 288 3 43 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 128 150 288 2 64 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 150 288 (Polychromatic418967fa.accept_17_8_14_16_1_6849 127
  150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 150 288 6 21 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 150 288
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 125 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 150 288 2 62 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 150 288 3 41 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 150 288 2 61 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 150 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 121 150 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 288 6 20 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 119 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 150 288 2 59 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 150 288 3 39 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 150 288 2 58 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 150 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 115 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 288 6 19 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 288
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 113 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 150 288 2 56 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 150 288 3 37 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 150 288 2 55 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 150 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 288 6 18 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 107 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 150 288 2 53 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 150 288 3 35 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 288 2 52 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 288 6 17 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 288
  (Polychromatic418967fa.accept_19_6_17_3_1_11186 101 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 150 288 2 50 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 150 288 3 33 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 150 288 2 49 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  97 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 288 6 16 25 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 95 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 150 288 2 47 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 150 288 3 31 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 150 288 2 46 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 288 (Polychromatic418967fa.accept_19_15_17_3_1_13760 91 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 288 6 15 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 150 288 2 44 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 150 288 3 29 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 150 288 2 43 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 288 (Polychromatic418967fa.accept_20_5_10_8_1_6397 85 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 150 288 6 14 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 288
  (Polychromatic418967fa.accept_13_5_7_2_1_852 83 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 288 2 41 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 150 288 3 27 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 288 2 40 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 150 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 288 6 13 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 288
  (Polychromatic418967fa.accept_19_1_17_3_1_1821 77 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 288 2 38 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 288 3 25 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 288 2 37 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 73 150
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 288 6 12 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 288
  (Polychromatic418967fa.accept_19_14_17_3_1_4137 71 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 150 288 2 35 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 150 288 3 23 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 288 2 34 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 288 6 11 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 288 2 32 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 150 288 3 21 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 288 2 31 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 150 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 288 6 10 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 288
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 59 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 150 288 2 29 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 288 3 19 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 288 2 28 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 288
  (Polychromatic418967fa.accept_20_15_10_8_1_6398 55 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 150 288 6 9 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 150 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 150 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 288 2 26 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 150 288 3 17 50 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 288 2 25 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 288
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 49 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 150 288 6 8 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 150 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 150 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 288 2 23 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 288 3 15 50 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 288 2 22 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 288
  (Polychromatic418967fa.accept_19_5_17_3_1_4152 43 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 288 6 7 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 150 288 (Polychromatic418967fa.accept_26_15_20_2_1_12368 41 150 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 288 2 20 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 288 3 13 50 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 288 2 19 75 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 288 6 6 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 150 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 150 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 288 2 17 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 288 3 11 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 288 2 16 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 288 6 5 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 150 288 (Polychromatic418967fa.accept_21_8_3_15_1_2875 29 150 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 288 2 14 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 288 3 9 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 288 2 13 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 288 6 4 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 150 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 288 2 11 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 288 3 7 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 288 2 10 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 288 6 3 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 288 (Polychromatic418967fa.accept_20_17_10_8_1_9374 17 150 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 288 2 8 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 288 3 5 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 288 2 7 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 288
  (Polychromatic418967fa.accept_22_13_18_2_1_10024 13 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 150 288 6 2 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 150 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 288 2 5 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 288 3 3 50 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 288 2 4 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 288
  (Polychromatic418967fa.accept_20_7_10_8_1_9411 7 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 288 6 1 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 150 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 288 2 2 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 288 3 1 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 288 2 1 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821
  1 150 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 149 288 (Eq.refl Bool.true) (allA_succ_of_accept 139 149 288 (accept_3_4 139 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 149 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 138 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 149 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 137 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 149 288 (accept_3_4 136 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 149 288 (Polychromatic418967fa.accept_19_2_16_3_1_7005 135 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 134 149 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 134 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 149 288 (accept_3_4 133 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214
  132 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 149 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 131 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 149 288 (accept_3_4 130 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 129 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 149 288 (Polychromatic418967fa.accept_17_9_13_16_1_3266 128 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 149 288 (accept_3_4 127 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 149 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 126 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 149 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 125 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 149 288 (accept_3_4 124 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 149 288 (Polychromatic418967fa.accept_21_18_2_15_1_5737 123 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 122 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 122 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 149 288 (accept_3_4 121 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 149 288 (Polychromatic418967fa.accept_19_6_16_3_1_1801 120
  149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 149 288
  (Polychromatic418967fa.accept_19_5_16_3_1_1820 119 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 149 288 (accept_3_4 118 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 149 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 117 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 149 288
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 116 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 149 288 (accept_3_4 115 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 149 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 114 149 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 149 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 113 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 149 288 (accept_3_4 112 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 149 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 111 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 149 288 (Polychromatic418967fa.accept_19_15_16_3_1_8409 110 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 149 288 (accept_3_4 109 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 149 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 107 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 149 288 (accept_3_4 106 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 149 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 105 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 149 288 (accept_3_4 103 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 149 288 (Polychromatic418967fa.accept_21_18_2_15_1_5737 102
  149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 149 288 (accept_3_4 100 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 149 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 99 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 149 288 (Polychromatic418967fa.accept_25_23_24_13_1_17779 98 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 288 (accept_3_4 97 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 96 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 95 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 149 288 (accept_3_4 94 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 149 288 (Polychromatic418967fa.accept_19_17_16_3_1_8401 93 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 149 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 92 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 288 (accept_3_4 91 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 288
  (Polychromatic418967fa.accept_19_13_16_3_1_6983 89 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 149 288 (accept_3_4 88 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 149 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 86 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 288 (accept_3_4 85 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 84 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 149 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 288 (accept_3_4 82 149 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 149 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 288 (accept_3_4 79 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 288 (Polychromatic418967fa.accept_19_2_16_3_1_7005 78 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 288 (accept_3_4 76 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 75 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 74 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 288 (accept_3_4 73 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 288 (Polychromatic418967fa.accept_19_15_16_3_1_8409 72 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 71 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 288 (accept_3_4 70 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 288
  (Polychromatic418967fa.accept_23_22_11_12_1_16205 68 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 149 288 (accept_3_4 67 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 149 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 288 (Polychromatic418967fa.accept_23_19_11_12_1_17778 65
  149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 288 (accept_3_4 64
  149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 288
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 288 (accept_3_4 61 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 60 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 288 (accept_3_4 58 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 56 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 288 (accept_3_4 55 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 288
  (Polychromatic418967fa.accept_13_1_6_2_1_377 53 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 288 (accept_3_4 52 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 288 (Polychromatic418967fa.accept_21_8_2_15_1_17727 50 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 288 (accept_3_4 49 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 288 (accept_3_4 46 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 288 (accept_3_4 43 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 288 (Polychromatic418967fa.accept_19_4_16_3_1_4175 42 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 288 (accept_3_4 40 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 288 (Polychromatic418967fa.accept_19_1_16_3_1_11223 39 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 288 (accept_3_4 37 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 288 (accept_3_4 34 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 288 (Polychromatic418967fa.accept_19_14_16_3_1_15089 33 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 288 (accept_3_4 31 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437
  30 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 288
  (Polychromatic418967fa.accept_14_1_9_8_1_2863 29 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 288 (accept_3_4 28 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 288 (accept_3_4 25 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 288
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 288 (accept_3_4 22 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 288 (accept_3_4 19 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 288 (Polychromatic418967fa.accept_19_18_16_3_1_1803 18 149 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 288 (accept_3_4 16 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 288 (accept_3_4 13 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 149
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 288 (accept_3_4 10 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 288 (accept_3_4 7 149 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 288
  (Polychromatic418967fa.accept_19_5_16_3_1_1820 5 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 288 (accept_3_4 4 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 149 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 288 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 288 (accept_3_4 1 149 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 149
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 141 148 288 (Eq.refl Bool.true) (allA_succ_of_gcd 140 148 288 4 35 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 148 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 139 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 148 288 2 69 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 148 288 (accept_3_5 137 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 148 288 4 34 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 148 288 (Polychromatic418967fa.accept_22_3_16_2_1_10045 135 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 148 288 2 67 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 148 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 133 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 148 288 4 33 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 148 288 (accept_3_5 131 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 148 288 2 65 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 148 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 129 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 148 288 4 32 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 148 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 127 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 148 288 2 63 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 148 288 (accept_3_5 125 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 148 288 4 31 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 148 288 (Polychromatic418967fa.accept_19_9_15_3_1_12536 123 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 148 288 2 61 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 148 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 121 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 148 288 4 30 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 148 288 (accept_3_5 119 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 148 288 2 59 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 148 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 117 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 148 288 4 29 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 148 288
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 115 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 148 288 2 57 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 148 288 (accept_3_5 113 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 148 288 4 28 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 148 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 111 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 148 288 2 55 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 148 288
  (Polychromatic418967fa.accept_25_9_23_13_1_17777 109 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 148 288 4 27 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 148 288 (accept_3_5 107 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 148 288 2 53 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 148 288 (Polychromatic418967fa.accept_19_10_15_3_1_5470 105 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 288 4 26 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 103 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 148 288 2 51 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 148 288 (accept_3_5 101 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 288 4 25 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 99 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 288 2 49 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 288
  (Polychromatic418967fa.accept_22_9_16_2_1_8457 97 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 288 4 24 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 288 (accept_3_5 95 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 288 2 47 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 288 (Polychromatic418967fa.accept_19_17_15_3_1_4174 93 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 288 4 23 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 288
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 91 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 288 2 45 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 288 (accept_3_5 89 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 288 4 22 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 87 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 288 2 43 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 288 4 21 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 288 (accept_3_5 83 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 288 2 41 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 81 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 288 4 20 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 288
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 79 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 148 288 2 39 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 148 288 (accept_3_5 77 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 288 4 19 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 288 (Polychromatic418967fa.accept_13_10_5_2_1_1477 75 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 288 2 37 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 288
  (Polychromatic418967fa.accept_19_16_15_3_1_8408 73 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 148 288 4 18 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 148 288 (accept_3_5 71 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 288 2 35 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 69 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 288 4 17 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 288
  (Polychromatic418967fa.accept_19_10_15_3_1_5470 67 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 148 288 2 33 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 148 288 (accept_3_5 65 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 288 4 16 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 288 2 31 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 288
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 288 4 15 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 288 (accept_3_5 59 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 288 2 29 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 288 4 14 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 55 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 288 2 27 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 288 (accept_3_5 53 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 288 4 13 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 288 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 288 2 25 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 288
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 288 4 12 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 288 (accept_3_5 47 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 288 2 23 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 288 (Polychromatic418967fa.accept_17_11_12_16_1_3219 45 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 288 4 11 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 288
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 288 2 21 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 288 (accept_3_5 41 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 288 4 10 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 288 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 148 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 288 2 19 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 288
  (Polychromatic418967fa.accept_19_18_15_3_1_5548 37 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 148 288 4 9 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 148 288 (accept_3_5 35 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 288 2 17 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 148 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 288 4 8 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 288
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 31 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 288 2 15 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 288 (accept_3_5 29 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 288 4 7 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 288 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 148 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 288 2 13 74 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 288
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 288 4 6 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 288 (accept_3_5 23 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 288 2 11 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 288 (Polychromatic418967fa.accept_23_21_10_12_1_14591 21 148 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 288 4 5 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 288 2 9 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 288 (accept_3_5 17 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 288 4 4 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 288 (Polychromatic418967fa.accept_25_15_23_13_1_17715 15 148 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 288 2 7 74 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 288
  (Polychromatic418967fa.accept_17_13_12_16_1_6908 13 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 288 4 3 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 288 (accept_3_5 11 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 288 2 5 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 148 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 288 4 2 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 288 (Polychromatic418967fa.accept_13_7_5_2_1_401 7
  148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 288 2 3 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 288 (accept_3_5 5
  148 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 288 4 1 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 288
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 148 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 148 288 2 1 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 148 288 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 148 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 148
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 142 147 288 (Eq.refl Bool.true) (allA_succ_of_gcd 141 147 288 3 47 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 140 147 288
  (Polychromatic418967fa.accept_19_7_14_3_1_1793 140 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 139 147 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 139 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 138 147 288 3 46 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 147 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 137 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 136 147 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 136 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 135 147 288 3 45 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 134 147 288
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 134 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 147 288 (Polychromatic418967fa.accept_15_13_12_3_1_1180 133 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 147 288 3 44 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 147 288
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 131 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 147 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 130 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 129 147 288 3 43 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 147 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 128 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 127 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 147 288 3 42 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 147 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 125 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 147 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 124 147 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 123 147 288 3 41 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 147 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 122 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 147 288 (Polychromatic418967fa.accept_19_7_14_3_1_1793 121 147 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 147 288 3 40 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 119 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 147 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 118 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 147 288 3 39 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599
  116 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 115 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 147 288 3 38 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 147 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 113 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 147 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 112 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 147 288 3 37 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 147 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 110 147 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 109 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 147 288 3 36 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 147 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 107 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 147 288
  (Polychromatic418967fa.accept_19_11_14_3_1_8426 106 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 147 288 3 35 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 147 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 104 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 288
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 103 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 147 288 3 34 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 147 288 (Polychromatic418967fa.accept_20_1_7_8_1_4877 101 147 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 288
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 100 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 147 288 3 33 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 147 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 98 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 97 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 147 288 3 32 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 95 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 94 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 147 288 3 31 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 147 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 92 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 288
  (Polychromatic418967fa.accept_23_22_9_12_1_17776 91 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 147 288 3 30 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 147 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 89 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 88 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 147 288 3 29 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 147 288 (Polychromatic418967fa.accept_11_9_4_2_1_600 86 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 85 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 147 288 3 28 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 83 147 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 82 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 147 288 3 27 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 147 288 (Polychromatic418967fa.accept_17_12_11_16_1_6903 80 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 79 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 147 288 3 26 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 147 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 76 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 147 288 3 25 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 147 288 (Polychromatic418967fa.accept_19_17_14_3_1_5572 74 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 73 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 147 288 3 24 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 147 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 70 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 147 288 3 23 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 147 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 68 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 147 288 3 22 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 64 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 288 3 21 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 147 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 62 147 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599
  61 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 288 3 20 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 58 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 288 3 19 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 147 288
  (Polychromatic418967fa.accept_17_5_11_16_1_3257 56 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 55 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 288 3 18 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 53 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 288 3 17 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599
  50 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 288 3 16 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 288
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 46 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 147 288 3 15 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 147 288 (Polychromatic418967fa.accept_13_5_4_2_1_846 44 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 288
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 43 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 288 3 14 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 147 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 288
  (Polychromatic418967fa.accept_26_14_17_2_1_17775 40 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 147 288 3 13 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 147 288 (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 147 288 3 12 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 288
  (Polychromatic418967fa.accept_14_6_7_8_1_624 34 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 288 3 11 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 288 3 10 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 288
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 147 288 3 9 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 288 (Polychromatic418967fa.accept_19_7_14_3_1_1793 26 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 147
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 288 3 8 49 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 288
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 288 (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 288 3 7 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 288 (Polychromatic418967fa.accept_11_9_4_2_1_600
  20 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 288 3 6 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 288 (Polychromatic418967fa.accept_19_16_14_3_1_11194 16
  147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 288 3 5 49 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 288
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 14 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 147 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 288 3 4 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 288 (Polychromatic418967fa.accept_20_10_7_8_1_4923 10 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 288 3 3 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 288 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 147 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 288
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 147 288 3 2 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 288 (Polychromatic418967fa.accept_27_4_12_18_1_17774 4 147
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 288 3 1 49 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 288
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 147 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 147 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 143 146 288 (Eq.refl Bool.true) (allA_succ_of_gcd 142 146 288 2 71 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 141 146 288
  (Polychromatic418967fa.accept_13_11_3_2_1_863 141 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 140 146 288 2 70 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 139 146 288 (accept_3_4 139 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 146 288 2 69 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 146 288 (Polychromatic418967fa.accept_19_4_13_3_1_5571 137 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 146 288 2 68 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 146 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 135 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 146 288 2 67 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 146 288 (accept_3_4 133 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 146 288 2 66 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 146 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 131 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 146 288 2 65 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 146 288
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 129 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 128 146 288 2 64 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 127 146 288 (accept_3_4 127 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 146 288 2 63 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 146 288 (Polychromatic418967fa.accept_17_6_10_16_1_9453 125 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 146 288 2 62 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 146 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 123 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 146 288 2 61 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 146 288 (accept_3_4 121 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 146 288 2 60 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 146 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 119 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 146 288 2 59 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 146 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 117 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 146 288 2 58 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 146 288 (accept_3_4 115 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 146 288 2 57 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 146 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 113 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 146 288 2 56 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 146 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 111 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 146 288 2 55 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 146 288 (accept_3_4 109 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 146 288 2 54 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 146 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 146 288 2 53 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 146 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 105 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 146 288 2 52 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 146 288 (accept_3_4 103 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 146 288 2 51 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 146 288 (Polychromatic418967fa.accept_13_10_3_2_1_4728 101 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 146 288 2 50 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 146 288
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 99 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 146 288 2 49 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 146 288 (accept_3_4 97 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 146 288 2 48 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 146 288 (Polychromatic418967fa.accept_25_20_21_13_1_17690 95 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 288 2 47 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 93 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 288 2 46 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 288 (accept_3_4 91 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 288 2 45 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 288 2 44 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 288
  (Polychromatic418967fa.accept_13_9_3_2_1_399 87 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 288 2 43 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 288 (accept_3_4 85 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 288 2 42 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 288 2 41 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 81 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 288 2 40 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 288 (accept_3_4 79 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 288 2 39 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 288 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 288 2 38 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 288 2 37 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 288 (accept_3_4 73 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 288 2 36 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 288 (Polychromatic418967fa.accept_33_5_14_24_1_17773 71 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 288 2 35 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 288
  (Polychromatic418967fa.accept_19_12_13_3_1_5447 69 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 146 288 2 34 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 146 288 (accept_3_4 67 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 288 2 33 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 288 2 32 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 288 2 31 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 288 (accept_3_4 61 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 288 2 30 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 288 2 29 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 288
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 288 2 28 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 288 (accept_3_4 55 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 288 2 27 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 288 2 26 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 288 2 25 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 288 (accept_3_4 49 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 288 2 24 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 288 2 23 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 288 2 22 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 288 (accept_3_4 43 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 288 2 21 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 288 (Polychromatic418967fa.accept_17_7_10_16_1_5582 41 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 288 2 20 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 288
  (Polychromatic418967fa.accept_21_18_20_15_1_8916 39 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 146 288 2 19 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 146 288 (accept_3_4 37 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 288 2 18 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 288 2 17 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 288 2 16 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 288 (accept_3_4 31 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 288 2 15 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 288 2 14 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 288 2 13 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 288 (accept_3_4 25 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 288 2 12 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 146 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 288 2 11 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 288
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 288 2 10 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 288 (accept_3_4 19 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 288 2 9 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 288 (Polychromatic418967fa.accept_25_17_21_13_1_9067 17 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 288 2 8 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 288
  (Polychromatic418967fa.accept_29_15_1_27_1_17772 15 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 146 288 2 7 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 146 288 (accept_3_4 13 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 288 2 6 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 288 2 5 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 288 2 4 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 288 (accept_3_4 7 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  288 2 3 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 288 2 2 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 146 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 288 2 1 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 288 (accept_3_4 1 146 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 144 145 288 (Eq.refl Bool.true) (allA_succ_of_accept 143 145 288 (accept_3_5 143 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 142 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 142 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 141 145 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 141 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 140 145 288 (accept_3_5 140 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 139 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 139 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 145 288 (Polychromatic418967fa.accept_21_12_19_15_1_8942 138
  145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 145 288 (accept_3_5 137
  145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 145 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 136 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 145 288 (Polychromatic418967fa.accept_19_2_12_3_1_5446 135 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 145 288 (accept_3_5 134 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 133 145 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 133 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 145 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 132 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 145 288 (accept_3_5 131 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 130 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 129 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 145 288 (accept_3_5 128 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 145 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 127 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 145 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 126 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 145 288 (accept_3_5 125 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 145 288 (Polychromatic418967fa.accept_19_10_12_3_1_12558 124 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418
  123 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 145 288 (accept_3_5
  122 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 145 288
  (Polychromatic418967fa.accept_19_7_12_3_1_4169 121 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 145 288 (Polychromatic418967fa.accept_22_10_13_2_1_13227 120 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 145 288 (accept_3_5 119 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 118 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 145 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 117 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 145 288 (accept_3_5 116 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 115 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 145 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 114 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 145 288 (accept_3_5 113 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 112 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 145 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 111 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 145 288 (accept_3_5 110 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 109 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 108 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 288 (accept_3_5 107 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 288 (Polychromatic418967fa.accept_19_11_12_3_1_8407 106
  145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 288
  (Polychromatic418967fa.accept_19_10_12_3_1_12558 105 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 145 288 (accept_3_5 104 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 145 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 103 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418
  102 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 288 (accept_3_5
  101 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 288
  (Polychromatic418967fa.accept_26_22_15_2_1_17686 100 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 145 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 99 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 288 (accept_3_5 98 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 96 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 145 288 (accept_3_5 95 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 145 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 93 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 288 (accept_3_5 92 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 288 (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 145 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 145 288 (accept_3_5 89 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 288 (accept_3_5 86 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 145 288 (Polychromatic418967fa.accept_19_9_12_3_1_2950 85 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 288
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 84 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 145 288 (accept_3_5 83 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 82 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 288 (accept_3_5 80 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 145 288 (Polychromatic418967fa.accept_25_4_20_13_1_17711 79 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 288
  (Polychromatic418967fa.accept_17_10_9_16_1_5607 78 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 145 288 (accept_3_5 77 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 288 (Polychromatic418967fa.accept_20_15_5_8_1_4920 75 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 288 (accept_3_5 74 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 288 (accept_3_5 71 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 145 288 (Polychromatic418967fa.accept_19_13_12_3_1_5540 70 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 288 (accept_3_5 68 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 288 (accept_3_5 65 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 288 (Polychromatic418967fa.accept_17_13_9_16_1_3254 64 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 288 (accept_3_5 62 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 288 (Polychromatic418967fa.accept_17_10_9_16_1_5607 61 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 288 (accept_3_5 59 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 288 (accept_3_5 56 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 54 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 288 (accept_3_5 53 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 288 (accept_3_5 50 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 288 (Polychromatic418967fa.accept_19_11_12_3_1_8407 49 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 288 (accept_3_5 47 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 288 (accept_3_5 44 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 288 (accept_3_5 41 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 288 (Polychromatic418967fa.accept_17_6_9_16_1_4410 40 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 288 (accept_3_5 38 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 288 (accept_3_5 35 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 145 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 288 (accept_3_5 32 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 288 (Polychromatic418967fa.accept_17_13_9_16_1_3254 30 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 288 (accept_3_5 29 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 288 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 288 (accept_3_5 26 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 288 (accept_3_5 23 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 288
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 288 (accept_3_5 20 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 288 (Polychromatic418967fa.accept_22_19_13_2_1_17718 19 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 288 (accept_3_5 17 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 288 (Polychromatic418967fa.accept_22_16_13_2_1_13228 16
  145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 288
  (Polychromatic418967fa.accept_19_15_12_3_1_11213 15 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 145 288 (accept_3_5 14 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 288 (accept_3_5 11 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 145 288 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 288 (accept_3_5 8 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 145 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 145 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 288 (accept_3_5 5 145
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 288 (accept_3_5 2 145 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 288 (Polychromatic418967fa.accept_21_1_19_15_1_8914 1 145 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 144 288 (allA_succ_of_accept 143 144 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 143 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 142 144 288 2 71 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 141 144 288 3 47 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 140 144 288 4 35 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 144 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 139 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 144 288 6 23 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 144 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 137 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 144 288 8 17 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 135 144 288 9 15 16 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 134 144 288 2 67 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 144 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 133 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 144 288 12 11 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 144 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 131 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 144 288 2 65 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 129 144 288 3 43 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 128 144 288 16 8 9 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 144 288
  (Polychromatic418967fa.accept_19_13_11_3_1_5465 127 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 144 288 18 7 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 144 288 (Polychromatic418967fa.accept_15_5_9_3_1_528 125 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 144 288 4 31 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 123 144 288 3 41 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 122 144 288 2 61 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 144 288
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 121 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 144 288 24 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 144 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 119 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 144 288 2 59 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 144 288 9 13 16 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 144 288 4 29 36 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 144 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 115 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 144 288 6 19 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 144 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 113 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 144 288 16 7 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 111 144 288 3 37 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 110 144 288 2 55 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 144 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 109 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 144 288 36 3 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 107 144 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 107 144 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 288 2 53 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 144 288 3 35 48 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 144 288 8 13 18 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 144 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 103 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 144 288 6 17 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 144 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 144 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 288 4 25 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 144 288 9 11 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 288 2 49 72 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 288
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 97 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 144 288 48 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 144 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 95 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 288 2 47 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 144 288 3 31 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 288 4 23 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 288 18 5 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 144 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 288 8 11 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 144 288 3 29 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 288 2 43 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 288
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 85 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 288 12 7 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 83 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 288 2 41 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 144 288 9 9 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 288 16 5 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 288 6 13 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 77 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 288 4 19 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 144 288 3 25 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 288 2 37 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 288 72 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 288 (Polychromatic418967fa.accept_13_6_1_2_1_1464 71 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 288 2 35 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 144 288 3 23 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 288 4 17 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 67 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 288 6 11 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 288 16 4 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 144 288 9 7 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 288 2 31 72 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 288 12 5 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 144 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 288 2 29 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 144 288 3 19 48 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 288 8 7 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 288
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 288 18 3 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 288 4 13 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 288 3 17 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 288 2 25 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 288 48 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 288 2 23 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 288 9 5 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 288 4 11 36 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 288 6 7 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 288 (Polychromatic418967fa.accept_17_7_8_16_1_6966 41 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 288 8 5 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 288 3 13 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 288 2 19 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 288
  (Polychromatic418967fa.accept_19_18_11_3_1_11183 37 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 144 288 36 1 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 288 2 17 72 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 288 3 11 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 288 16 2 9 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 288 6 5 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 288 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 288 4 7 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 288 9 3 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 288 2 13 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 288
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 288 24 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 144 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 288 2 11 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 288 3 7 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 288 4 5 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19
  144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 288 18 1 8 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 288 16 1 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 144 288 3 5 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 144 288 2 7 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 144 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 144 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 288 12 1 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 11 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 288 2 5 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 288 9 1 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 144 288 8 1 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 288 (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 144 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 288 6 1 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 288 4 1 36 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 288 3 1 48 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 288 2 1 72 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 288
  (Polychromatic418967fa.accept_19_1_11_3_1_5463 1 144 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 143 288 (allA_succ_of_accept 142 143 288 (accept_3_4 142 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 141 143 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 141 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 140 143 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 140 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 143 288 (accept_3_4 139 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 143 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 138 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 137 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 143 288 (accept_3_4 136 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 135 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 143 288
  (Polychromatic418967fa.accept_19_1_10_3_1_8398 134 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 143 288 (accept_3_4 133 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 143 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 132 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424
  131 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 143 288 (accept_3_4
  130 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 143 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 129 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 128 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 288 (accept_3_4 127 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 143 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 126 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 125 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 143 288 (accept_3_4 124 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 123 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 143 288 (Polychromatic418967fa.accept_17_3_7_16_1_3251 122 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 288 (accept_3_4 121 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 288 (Polychromatic418967fa.accept_25_20_18_13_1_17771 120
  143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 143 288
  (Polychromatic418967fa.accept_19_5_10_3_1_5460 119 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 143 288 (accept_3_4 118 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 117 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 116 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 143 288 (accept_3_4 115 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 143 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 114 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 143 288 (Polychromatic418967fa.accept_20_13_3_8_1_4865 113 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 288 (accept_3_4 112 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 111 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 110 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 143 288 (accept_3_4 109 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 143 288 (Polychromatic418967fa.accept_17_6_7_16_1_6836 108 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 143 288 (accept_3_4 106 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 143 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 105 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 288
  (Polychromatic418967fa.accept_19_9_10_3_1_1738 104 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 143 288 (accept_3_4 103 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 101 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 288 (accept_3_4 100 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 288
  (Polychromatic418967fa.accept_15_9_8_3_1_557 99 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 143 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 98 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 288 (accept_3_4 97 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 95
  143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 288 (accept_3_4 94
  143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 143 288 (Polychromatic418967fa.accept_21_8_17_15_1_2834 92 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 288 (accept_3_4 91 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 288 (Polychromatic418967fa.accept_21_6_17_15_1_2833 90 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 288 (accept_3_4 88 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 87 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 288 (accept_3_4 85 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 84 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 288
  (Polychromatic418967fa.accept_19_7_10_3_1_4149 83 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 288 (accept_3_4 82 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 80 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 288 (accept_3_4 79 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 288 (Polychromatic418967fa.accept_17_10_7_16_1_6841 78 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 288
  (Polychromatic418967fa.accept_19_1_10_3_1_8398 77 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 288 (accept_3_4 76 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 288 (accept_3_4 73 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 71 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 288 (accept_3_4 70 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 288 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 288 (accept_3_4 67 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 288 (accept_3_4 64 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 288 (Polychromatic418967fa.accept_22_19_11_2_1_17770 63 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 288 (Polychromatic418967fa.accept_19_5_10_3_1_5460 62 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 288 (accept_3_4 61 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 288
  (Polychromatic418967fa.accept_17_8_7_16_1_9508 59 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 288 (accept_3_4 58 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 57 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 288 (accept_3_4 55 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 288 (accept_3_4 52 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 50 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 288 (accept_3_4 49 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 288 (Polychromatic418967fa.accept_21_6_17_15_1_2833 48 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 288 (accept_3_4 46 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 288 (accept_3_4 43 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 288 (accept_3_4 40 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 288 (Polychromatic418967fa.accept_20_18_3_8_1_7903 38 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 288 (accept_3_4 37 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 288 (accept_3_4 34 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 288 (accept_3_4 31 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 288
  (Polychromatic418967fa.accept_21_8_17_15_1_2834 29 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 143 288 (accept_3_4 28 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 143 288 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 288 (accept_3_4 25 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 288 (Polychromatic418967fa.accept_15_9_8_3_1_557
  24 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 288 (accept_3_4 22 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 20 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 288 (accept_3_4 19 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 288
  (Polychromatic418967fa.accept_22_17_11_2_1_16241 17 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 288 (accept_3_4 16 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 288 (Polychromatic418967fa.accept_20_14_3_8_1_4914 14 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 288 (accept_3_4 13 143
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 288 (accept_3_4 10 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 143 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 143 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 288 (Polychromatic418967fa.accept_17_8_7_16_1_9508
  8 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 288 (accept_3_4 7
  143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 143 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 288 (accept_3_4 4 143 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 143 288 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 143 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 288 (accept_3_4 1 143 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 142 288 (allA_succ_of_accept 141 142 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 141 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 140 142 288 2 70 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 142 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 139 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 142 288 2 69 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 142 288 (accept_3_5 137 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 142 288 2 68 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 142 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 135 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 142 288 2 67 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 142 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 133 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 142 288 2 66 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 142 288 (accept_3_5 131 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 142 288 2 65 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 142 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 129 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 142 288 2 64 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 142 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 127 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 142 288 2 63 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 142 288 (accept_3_5 125 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 142 288 2 62 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 142 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 123 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 142 288 2 61 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 142 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 121 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 142 288 2 60 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 142 288 (accept_3_5 119 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 142 288 2 59 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 142 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 117 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 142 288 2 58 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 142 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 115 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 142 288 2 57 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 142 288 (accept_3_5 113 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 142 288 2 56 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 142 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 111 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 142 288 2 55 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 142 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 109 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 142 288 2 54 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 142 288 (accept_3_5 107 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 142 288 2 53 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 142 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 105 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 142 288 2 52 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 288
  (Polychromatic418967fa.accept_23_11_4_12_1_17769 103 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 142 288 2 51 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 142 288 (accept_3_5 101 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 288 2 50 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 99 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 288 2 49 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 97 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 288 2 48 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 288 (accept_3_5 95 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 288 2 47 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 288 (Polychromatic418967fa.accept_21_9_16_15_1_9014 93 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 288 2 46 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 288
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 91 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 142 288 2 45 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 142 288 (accept_3_5 89 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 288 2 44 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 288 2 43 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 288 2 42 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 288 (accept_3_5 83 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 288 2 41 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 81 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 288 2 40 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 79 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 288 2 39 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 288 (accept_3_5 77 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 288 2 38 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 288 2 37 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 288 2 36 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 288 (accept_3_5 71 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 288 2 35 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 288 2 34 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 67 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 288 2 33 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 288 (accept_3_5 65 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 288 2 32 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 288 (Polychromatic418967fa.accept_19_6_9_3_1_15079 63 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 288 2 31 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 288
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 61 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 142 288 2 30 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 142 288 (accept_3_5 59 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 288 2 29 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 288 2 28 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 288 2 27 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 288 (accept_3_5 53 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 288 2 26 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 288 (Polychromatic418967fa.accept_19_13_9_3_1_9806 51 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 288 2 25 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 288
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 142 288 2 24 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 142 288 (accept_3_5 47 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 288 2 23 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 288 2 22 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 288
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 288 2 21 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 288 (accept_3_5 41 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 288 2 20 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 288 (Polychromatic418967fa.accept_21_18_16_15_1_2864 39 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 288 2 19 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 288
  (Polychromatic418967fa.accept_19_18_9_3_1_8430 37 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 288 2 18 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 288 (accept_3_5 35 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 288 2 17 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 288 (Polychromatic418967fa.accept_19_14_9_3_1_13821 33 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 288 2 16 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 288 2 15 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 288 (accept_3_5 29 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 288 2 14 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 288 2 13 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 288 2 12 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 288 (accept_3_5 23 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 288 2 11 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 288 (Polychromatic418967fa.accept_22_21_10_2_1_8494 21 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 288 2 10 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 288 2 9 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 288 (accept_3_5 17 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 288 2 8 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 288 2 7 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 288 2 6 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 288 (accept_3_5 11 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 288 2 5 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 142 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 288 2 4 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 288 2 3 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 288 (accept_3_5 5 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  288 2 2 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 288 2 1 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 142 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  288))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 141 288 (allA_succ_of_accept 140 141 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 140 141 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 141 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 139 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 141 288 3 46 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 141 288 (Polychromatic418967fa.accept_17_1_5_16_1_5589 137 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 141 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 136 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 135 141 288 3 45 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 134 141 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 134 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 141 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 133 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 141 288 3 44 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 141 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 131 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 141 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 130 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 129 141 288 3 43 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 128 141 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 128 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 288
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 127 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 141 288 3 42 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 141 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 125 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 141 288
  (Polychromatic418967fa.accept_23_9_3_12_1_6308 124 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 123 141 288 3 41 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 122 141 288 (Polychromatic418967fa.accept_25_22_16_13_1_17768 122 141 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 121 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 141 288 3 40 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 119 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 141 288
  (Polychromatic418967fa.accept_19_4_8_3_1_8416 118 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 141 288 3 39 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 141 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 116 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 115 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 141 288 3 38 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 141 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 113 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 141 288
  (Polychromatic418967fa.accept_19_17_8_3_1_11211 112 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 141 288 3 37 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 141 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 110 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 109 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 141 288 3 36 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 141 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 107 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 141 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 106 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 141 288 3 35 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 141 288 (Polychromatic418967fa.accept_17_2_5_16_1_1264 104 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 103 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 141 288 3 34 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 141 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 101 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 141 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 100 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 141 288 3 33 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 141 288 (Polychromatic418967fa.accept_20_18_1_8_1_9326 98 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 288
  (Polychromatic418967fa.accept_25_22_16_13_1_17768 97 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 141 288 3 32 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 141 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 95 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 94 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 141 288 3 31 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 141 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 92 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873
  91 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 141 288 3 30 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 141 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 89 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 88 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 141 288 3 29 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 141 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 86 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 288 (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 141 288 3 28 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 141 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  83 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 82 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 141 288 3 27 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 141 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 80 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755
  79 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 141 288 3 26 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 141 288
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 77 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 76 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 141 288 3 25 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 141 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491
  74 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 73 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 141 288 3 24 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 141 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 71 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 70 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 141 288 3 23 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 68 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 288
  (Polychromatic418967fa.accept_20_7_1_8_1_10806 67 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 141 288 3 22 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 141 288 (Polychromatic418967fa.accept_14_9_1_8_1_2849 65 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 288
  (Polychromatic418967fa.accept_27_10_6_18_1_15978 64 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 141 288 3 21 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 141 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 288
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 61 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 288 3 20 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 59 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 288 (Polychromatic418967fa.accept_14_2_1_8_1_650
  58 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 141 288 3 19 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 141 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 288 3 18 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 288 (Polychromatic418967fa.accept_10_3_1_8_1_132
  53 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 288
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 52 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 288 3 17 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 50 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755
  49 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 288 3 16 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 288
  (Polychromatic418967fa.accept_20_7_1_8_1_10806 47 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 288 3 15 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 288 (Polychromatic418967fa.accept_14_2_1_8_1_650
  44 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 43 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 288 3 14 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 288
  (Polychromatic418967fa.accept_11_7_9_2_1_260 40 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 141 288 3 13 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 141 288 (Polychromatic418967fa.accept_17_4_5_16_1_3240 38 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 288 3 12 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 288
  (Polychromatic418967fa.accept_19_15_8_3_1_13786 34 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 141 288 3 11 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 141 288 (Polychromatic418967fa.accept_19_13_8_3_1_2906 32 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 288
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 288 3 10 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 288
  (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 141 288 3 9 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 141 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 141 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 288 3 8 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 141
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 288 3 7 47 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 288
  (Polychromatic418967fa.accept_15_5_6_3_1_525 20 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 288 3 6 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458
  17 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 288
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 288 3 5 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 288 (Polychromatic418967fa.accept_19_14_8_3_1_6981 14 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 141
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 288 3 4 47 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 288 3 3 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 288
  (Polychromatic418967fa.accept_29_8_25_27_1_17699 8 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 141 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 141 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 288 3 2 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 5
  141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 141 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 288 3 1 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 141 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 288 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 141 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_288_segment_001))))))))))))))))))))))))))))))))))))))


