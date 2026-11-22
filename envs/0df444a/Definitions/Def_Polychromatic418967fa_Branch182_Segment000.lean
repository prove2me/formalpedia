-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch182_Segment000
-- name    : Polychromatic418967fa_Branch182_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:28:19.709776+00:00
-- url     : https://prove2.me/theorems/fb9989c9-0c38-4df6-8bf3-6ad177236f3b
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

def Polychromatic418967fa.branch_182_segment_000 : allB 146 182 :=
  allB_succ' 38 145 182 (Eq.refl Bool.true) (allA_of_3_0 38 145 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  39 144 182 (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 182 2 19 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 182 (accept_3_2 37 144 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 182 2 18 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 182 (Polychromatic418967fa.accept_20_15_4_2_1_5914 35 144
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 182 2 17 72 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 182
  (Polychromatic418967fa.accept_21_12_18_14_1_8854 33 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 144 182 2 16 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 144 182 (accept_3_2 31 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 182 2 15 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 144 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 182 2 14 72 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 182 2 13 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 182 (accept_3_2 25 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 182 2 12 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 182 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 144 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 182 2 11 72 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 182
  (Polychromatic418967fa.accept_17_4_8_12_1_9165 21 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 182 2 10 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 182 (accept_3_2 19 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 182 2 9 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 182 2 8 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 182 (Polychromatic418967fa.accept_20_15_4_2_1_5914
  15 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 182 2 7 72 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 182
  (accept_3_2 13 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 182 2 6 72 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 182
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 182 2 5 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 182 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 144 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 182 2 4 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 182 (accept_3_2 7 144 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 182 2 3 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 144 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 144 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 182 2 2 72 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 182 (Polychromatic418967fa.accept_17_3_8_12_1_6573
  3 144 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 182 2 1 72 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 182 (accept_3_2 1
  144 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 182))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 143 182 (Eq.refl Bool.true) (allA_succ_of_gcd 39 143 182 13 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 143 182 (Polychromatic418967fa.accept_17_4_7_12_1_6556
  38 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 182 (accept_3_2 37
  143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 182
  (Polychromatic418967fa.accept_15_6_8_2_1_104 36 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 143 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 182 (accept_3_2 34 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 143 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 182 (Polychromatic418967fa.accept_9_5_8_2_1_409
  32 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 182 (accept_3_2 31
  143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 143 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 182 (accept_3_2 28 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 143 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 143 182 13 2 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 143 182 (accept_3_2 25 143 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 182 (accept_3_2 22 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 143 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 182 (accept_3_2 19 143 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 182 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18
  143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 182 (accept_3_2 16 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 143 182 13 1 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 143 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 182 (accept_3_2 10 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 143 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  8 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 182 (accept_3_2 7
  143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 143 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 182 (accept_3_2 4 143 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 143 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 182 (Polychromatic418967fa.accept_17_2_7_12_1_1078
  2 143 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 182 (accept_3_2 1
  143 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143 182)))))))))))))))))))))))))))))))))))))))) (allB_succ'
  41 142 182 (Eq.refl Bool.true) (allA_of_3_0 41 142 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 141 182
  (Eq.refl Bool.true) (allA_succ_of_accept 41 141 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 182 (accept_3_2 40 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 182 (accept_3_2 37 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 182 (accept_3_2 34 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 182 (accept_3_2 31 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 182 (accept_3_2 28 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 182 (accept_3_2 25 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 182 (Polychromatic418967fa.accept_17_7_5_12_1_1997 24 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 182 (accept_3_2 22 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 182
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 182 (accept_3_2 19 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 182 (accept_3_2 16 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 182 (accept_3_2 13 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 182 (accept_3_2 10 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 182 (accept_3_2 7 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 182 (accept_3_2 4 141 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 182
  (Polychromatic418967fa.accept_19_2_8_11_1_7701 2 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 182 (accept_3_2 1 141 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  182)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 140 182 (Eq.refl Bool.true) (allA_succ_of_gcd 42 140 182
  14 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140
  182 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 140 182 2 20 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 140 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 140 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 182 2 19 70 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 182 (accept_3_2 37 140 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 182 2 18 70 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 140 182 7 5 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 140 182 2 17 70 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 182 2 16 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 182 (accept_3_2 31 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 182 2 15 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 140 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 182 14 2 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 182
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 182 2 13 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 182 (accept_3_2 25 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 182 2 12 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 182 2 11 70 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 140 182 7 3 20 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 140 182 2 10 70 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 182 (accept_3_2 19
  140 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 182 2 9 70 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 140 182 2 8 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 140 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 140 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 182 14 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 182 (accept_3_2 13 140 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 182 2 6 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 182 2 5 70 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 182
  (Polychromatic418967fa.accept_17_9_4_12_1_2958 9 140 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 182 2 4 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 140 182 7 1 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 140 182 2 3 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 140 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 182 2 2 70 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 182 2 1 70 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 182 (accept_3_2 1 140 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 182))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  139 182 (Eq.refl Bool.true) (allA_of_3_0 44 139 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 138 182
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 182 2 22 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 182 (accept_3_2 43 138 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 138 182 2 21 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 138 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 138 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 182 2 20 69 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 182 2 19 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 182 (accept_3_2 37 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 182 2 18 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 182 2 17 69 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 182 2 16 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 182 (accept_3_2 31 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 182 2 15 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 182 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 138 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 182 2 14 69 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 182 2 13 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 182 (accept_3_2 25 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 182 2 12 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 182 2 11 69 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 182 2 10 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 182 (accept_3_2 19 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 182 2 9 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 182 2 8 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 182 2 7 69 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 182 (accept_3_2 13
  138 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 182 2 6 69 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 182
  (Polychromatic418967fa.accept_21_11_12_14_1_5670 11 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 138 182 2 5 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 138 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 138 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 182 2 4 69 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 182 (accept_3_2 7 138 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 182 2 3 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 182 2 2 69 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 138 182 2 1 69 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 182 (accept_3_2 1 138 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  182))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 137 182 (Eq.refl Bool.true) (allA_succ_of_accept 45
  137 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 182 (accept_3_2 43 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 182 (Polychromatic418967fa.accept_25_17_12_7_1_10518 42
  137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 182
  (Polychromatic418967fa.accept_19_3_4_11_1_469 41 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 182 (accept_3_2 40 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 182 (Polychromatic418967fa.accept_20_18_17_2_1_5941 38 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 182 (accept_3_2 37 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 182 (Polychromatic418967fa.accept_19_17_4_11_1_4731 36 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 182 (accept_3_2 34 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 182 (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 182 (accept_3_2 31 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 182 (Polychromatic418967fa.accept_17_13_1_12_1_7893 30 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 182
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 182 (accept_3_2 28 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 182 (Polychromatic418967fa.accept_19_7_4_11_1_3414 26 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 182 (accept_3_2 25 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 182 (accept_3_2 22 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 182 (accept_3_2 19 137 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 182
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 137 182 (accept_3_2 16 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 137 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 182 (accept_3_2 13 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 182
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 137 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 182 (accept_3_2 10 137 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 137 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 182 (accept_3_2 7 137
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 182
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 6 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 137 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 137 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 182 (accept_3_2 4 137 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 137 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441
  2 137 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 182 (accept_3_2 1
  137 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137 182))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 136 182 (Eq.refl Bool.true) (allA_of_3_0 47 136 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 48 135 182 (Eq.refl Bool.true) (allA_succ_of_accept 47 135 182 (Polychromatic418967fa.accept_6_5_3_2_1_68
  47 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 182 (accept_3_2 46
  135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 182 (Polychromatic418967fa.accept_20_4_15_2_1_223 44 135 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 182 (accept_3_2 43 135 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 182 (accept_3_2 40 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 182 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 182 (accept_3_2 37 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 182 (Polychromatic418967fa.accept_21_15_9_14_1_10462 36
  135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 182 (accept_3_2 34 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 182 (Polychromatic418967fa.accept_19_13_2_11_1_9083 32 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 182 (accept_3_2 31 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 182 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 135
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 182 (accept_3_2 28 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 182 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 182 (Polychromatic418967fa.accept_21_5_9_14_1_7247 26 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 182 (accept_3_2 25 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 135
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 182 (accept_3_2 22 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 182 (accept_3_2 19 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 135
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 182 (accept_3_2 16 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 182 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 182 (Polychromatic418967fa.accept_22_14_3_6_1_10517 14 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 182 (accept_3_2 13 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 182 (Polychromatic418967fa.accept_28_12_23_14_1_10516 12
  135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 182 (accept_3_2 10 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 135 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 182 (accept_3_2 7 135 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 182 (accept_3_2 4 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 135 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 182 (Polychromatic418967fa.accept_21_2_9_14_1_4189 2 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 182 (accept_3_2 1 135 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 182)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 134
  182 (Eq.refl Bool.true) (allA_succ_of_gcd 48 134 182 2 24 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 134 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 134 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 182 2 23 67 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 182
  (Polychromatic418967fa.accept_21_3_8_14_1_8864 45 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 182 2 22 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 182 (accept_3_2 43 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 182 2 21 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 134 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 182 2 20 67 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 182 2 19 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 182 (accept_3_2 37 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 182 2 18 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 134 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 182 2 17 67 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 182 2 16 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 182 (accept_3_2 31 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 182 2 15 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 182 (Polychromatic418967fa.accept_19_10_1_11_1_7532 29 134 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 182 2 14 67 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 182 2 13 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 182 (accept_3_2 25 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 182 2 12 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 134 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 182 2 11 67 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 182 2 10 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 182 (accept_3_2 19 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 182 2 9 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 134 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 182 2 8 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 182 2 7 67 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 182 (accept_3_2 13
  134 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 182 2 6 67 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 182
  (Polychromatic418967fa.accept_21_11_8_14_1_10515 11 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 134 182 2 5 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 134 182 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 134 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 182 2 4 67 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 182 (accept_3_2 7 134 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 182 2 3 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 134 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 182 2 2 67 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 182 2 1 67 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 182 (accept_3_2 1 134 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  182))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 133 182 (Eq.refl Bool.true) (allA_of_3_0 50 133
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 132 182 (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 182 2
  25 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132
  182 (accept_3_2 49 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 182 2 24 66 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 182
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 47 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 182 2 23 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 182 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 132 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 182 2 22 66 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 182 (accept_3_2 43 132 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 182 2 21 66 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 182 2 20 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 132 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 182 2 19 66 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 182 (accept_3_2 37 132 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 182 2 18 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 182 2 17 66 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 182
  (Polychromatic418967fa.accept_15_3_12_2_1_507 33 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 132 182 2 16 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 132 182 (accept_3_2 31 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 182 2 15 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 182 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 132 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 182 2 14 66 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 182
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 182 2 13 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 182 (accept_3_2 25 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 182 2 12 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 182 2 11 66 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 182 2 10 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 182 (accept_3_2 19 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 182 2 9 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 182 2 8 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 182
  (Polychromatic418967fa.accept_23_15_17_21_1_10514 15 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 182 2 7 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 182 (accept_3_2 13 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 182 2 6 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 182 (Polychromatic418967fa.accept_16_11_4_6_1_4422 11 132 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 182 2 5 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 182 (Polychromatic418967fa.accept_18_9_6_2_1_2619 9
  132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 182 2 4 66 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 182 (accept_3_2 7
  132 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 182 2 3 66 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 182 2 2 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 182 2 1 66 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 182 (accept_3_2 1 132 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 182))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 131 182 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 131 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 182
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 182 (accept_3_2 49 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 182 (Polychromatic418967fa.accept_19_9_17_11_1_2226 47 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 182 (accept_3_2 46 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 182 (accept_3_2 43 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 182 (accept_3_2 40 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 182
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 182 (accept_3_2 37 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 182 (accept_3_2 34 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 182 (accept_3_2 31 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 182 (accept_3_2 28 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 182 (accept_3_2 25 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 182 (accept_3_2 22 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 182 (accept_3_2 19 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 182 (accept_3_2 16 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 182
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 14 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 182 (accept_3_2 13 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 182 (Polychromatic418967fa.accept_16_11_3_6_1_4462 11 131
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 182 (accept_3_2 10 131
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 182 (accept_3_2 7 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 182 (accept_3_2 4 131 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 182
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 182 (accept_3_2 1 131 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  182)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 130 182 (Eq.refl Bool.true) (allA_of_3_0 53 130
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 129 182 (Eq.refl Bool.true) (allA_succ_of_accept 53 129
  182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 182 (accept_3_2 52 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 182 (accept_3_2 49 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 182 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 182 (accept_3_2 46 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 182 (Polychromatic418967fa.accept_18_9_3_2_1_3814 45 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 182 (accept_3_2 43 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 182 (accept_3_2 40 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 182 (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 182 (accept_3_2 37 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 129
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 182 (accept_3_2 34 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 182 (accept_3_2 31 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 182 (accept_3_2 28 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 182 (accept_3_2 25 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 182 (accept_3_2 22 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 182 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 182 (Polychromatic418967fa.accept_19_1_15_11_1_4712 20 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 182 (accept_3_2 19 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 129
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 182 (accept_3_2 16 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 182 (accept_3_2 13 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 182 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 182 (accept_3_2 10 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 182 (Polychromatic418967fa.accept_18_9_3_2_1_3814 9 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 182 (accept_3_2 7 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 182 (accept_3_2 4 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 182 (accept_3_2 1 129 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 182)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 128 182
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 128 182 2 27 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 128 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 128 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 182 2 26 64 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 182
  (Polychromatic418967fa.accept_15_6_8_2_1_104 51 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 182 2 25 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 182 (accept_3_2 49 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 182 2 24 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 128 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 182 2 23 64 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 182 2 22 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 182 (accept_3_2 43 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 182 2 21 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 128 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 182 2 20 64 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 182
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 182 2 19 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 182 (accept_3_2 37 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 182 2 18 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 128 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 182 2 17 64 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 182
  (Polychromatic418967fa.accept_21_12_2_14_1_10513 33 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 128 182 2 16 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 128 182 (accept_3_2 31 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 182 2 15 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 128 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 182 2 14 64 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 182
  (Polychromatic418967fa.accept_21_6_2_14_1_5688 27 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 182 2 13 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 182 (accept_3_2 25 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 182 2 12 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 182 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 128 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 182 2 11 64 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 182
  (Polychromatic418967fa.accept_15_6_8_2_1_104 21 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 182 2 10 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 182 (accept_3_2 19 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 182 2 9 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 128 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 182 2 8 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 182 (Polychromatic418967fa.accept_10_5_8_2_1_517
  15 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 182 2 7 64 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 182
  (accept_3_2 13 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 182 2 6 64 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 182 2 5 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 128 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 182 2 4 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 182 (accept_3_2 7 128 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 182 2 3 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 128 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 182 2 2 64 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 182 (Polychromatic418967fa.accept_19_3_14_11_1_2214
  3 128 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 182 2 1 64 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 182 (accept_3_2 1
  128 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 127 182 (Eq.refl Bool.true) (allA_of_3_0 56
  127 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 126 182 (Eq.refl Bool.true) (allA_succ_of_gcd 56 126
  182 14 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  126 182 (accept_3_2 55 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 182 2 27 63 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 182 2 26 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 126 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 182 2 25 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 126 182 7 7 18 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 182 2 24 63 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 182
  (Polychromatic418967fa.accept_23_1_11_21_1_10512 47 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 126 182 2 23 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 126 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 126 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 182 2 22 63 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 182 (accept_3_2 43 126 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 182 14 3 9 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 182 2 20 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 126 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 182 2 19 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 182 (accept_3_2 37 126 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 182 2 18 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 182 7 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 182 2 17 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 182 2 16 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 182 (accept_3_2 31 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 182 2 15 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 182 (Polychromatic418967fa.accept_19_10_12_11_1_7622 29 126 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 182 14 2 9 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 182 2 13 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 182 (accept_3_2 25 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 182 2 12 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 126 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 182 2 11 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 182 7 3 18 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 182 2 10 63 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 182 (accept_3_2 19 126 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 182 2 9 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 182
  (Polychromatic418967fa.accept_23_17_11_21_1_10511 17 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 126 182 2 8 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 126 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 126 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 182 14 1 9 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 182 (accept_3_2 13 126 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 182 2 6 63 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 182 2 5 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 182 2 4 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 182 7 1 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 182 2 3 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 182 (Polychromatic418967fa.accept_17_5_7_12_1_1951 5 126 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 182 2 2 63 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 182 2 1 63 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 182 (accept_3_2 1 126 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 125 182 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 125 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 125
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 182 (accept_3_2 55 125
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 182
  (Polychromatic418967fa.accept_22_10_15_6_1_10510 54 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 182 (accept_3_2 52 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 182 (accept_3_2 49 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 182 (accept_3_2 46 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 182 (accept_3_2 43 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 182 (accept_3_2 40 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 182 (accept_3_2 37 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 182 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 182 (accept_3_2 34 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 182 (accept_3_2 31 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 182 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 182 (accept_3_2 28 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 182
  (Polychromatic418967fa.accept_15_11_5_2_1_520 26 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 182 (accept_3_2 25 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 182 (accept_3_2 22 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 182 (accept_3_2 19 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 182 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 182 (accept_3_2 16 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 182 (accept_3_2 13 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 182 (accept_3_2 10 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 182 (accept_3_2 7 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 182 (accept_3_2 4 125 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 182
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 182 (accept_3_2 1 125 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 124 182 (Eq.refl Bool.true) (allA_of_3_0
  59 124 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 123 182 (Eq.refl Bool.true) (allA_succ_of_accept 59
  123 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 123 182 (accept_3_2 58 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 182 (Polychromatic418967fa.accept_23_10_8_21_1_2209 56 123
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 182 (accept_3_2 55 123
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 182
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 182 (accept_3_2 52 123 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 182 (accept_3_2 49 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 123 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 123 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 182 (accept_3_2 46 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 182 (accept_3_2 43 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 182 (accept_3_2 40 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 182
  (Polychromatic418967fa.accept_20_18_3_2_1_5929 38 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 182 (accept_3_2 37 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 123 182 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 123 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 182 (accept_3_2 34 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 182 (accept_3_2 31 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 123 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 182 (accept_3_2 28 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 182 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 123 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 182 (accept_3_2 25 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 123 182 (Polychromatic418967fa.accept_17_7_4_12_1_4084 24 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 182 (accept_3_2 22 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 182
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 182 (accept_3_2 19 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 182 (accept_3_2 16 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 182 (accept_3_2 13 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 182 (accept_3_2 10 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 182 (accept_3_2 7 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 182 (accept_3_2 4 123 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 182
  (Polychromatic418967fa.accept_16_2_11_6_1_737 2 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 182 (accept_3_2 1 123 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 122 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 122 182 2 30 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 182 (Polychromatic418967fa.accept_17_8_3_12_1_5354 59 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 182 2 29 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 182 2 28 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 182 (accept_3_2 55 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 182 2 27 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 122 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 182 2 26 61 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 182 2 25 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 182 (accept_3_2 49 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 182 2 24 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 182 (Polychromatic418967fa.accept_18_11_14_2_1_5058 47 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 182 2 23 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 182
  (Polychromatic418967fa.accept_19_7_8_11_1_3379 45 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 182 2 22 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 182 (accept_3_2 43 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 182 2 21 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 182 (Polychromatic418967fa.accept_17_7_3_12_1_4098 41 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 182 2 20 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 182 2 19 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 182 (accept_3_2 37 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 182 2 18 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 182 2 17 61 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 182 2 16 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 182 (accept_3_2 31 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 182 2 15 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 182 2 14 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 182
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 182 2 13 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 182 (accept_3_2 25 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 182 2 12 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 182 (Polychromatic418967fa.accept_21_2_17_14_1_5644 23 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 182 2 11 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 182 2 10 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 182 (accept_3_2 19 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 182 2 9 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 182 2 8 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 182 2 7 61 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 182 (accept_3_2 13
  122 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 182 2 6 61 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 182
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 182 2 5 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 182 (Polychromatic418967fa.accept_19_9_8_11_1_6072 9 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 182 2 4 61 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 182 (accept_3_2 7 122 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 182 2 3 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 122 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 182 2 2 61 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 182 2 1 61 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 182 (accept_3_2 1 122 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 121 182 (Eq.refl Bool.true)
  (allA_of_3_0 62 121 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 120 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 120 182 2 31 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 182 (accept_3_2 61 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 182 2 30 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 120 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 182 2 29 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 182
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 57 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 182 2 28 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 182 (accept_3_2 55 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 182 2 27 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 182 2 26 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 182 2 25 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 182 (accept_3_2 49 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 182 2 24 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 182 (Polychromatic418967fa.accept_17_13_1_12_1_7893 47 120 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 182 2 23 60 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 182
  (Polychromatic418967fa.accept_21_3_15_14_1_5722 45 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 120 182 2 22 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 120 182 (accept_3_2 43 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 182 2 21 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 120 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 182 2 20 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 182
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 182 2 19 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 182 (accept_3_2 37 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 182 2 18 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 182 2 17 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 182 2 16 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 120 182 (accept_3_2 31 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 182 2 15 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 182 (Polychromatic418967fa.accept_21_8_15_14_1_4176 29 120 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 182 2 14 60 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 182
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 182 2 13 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 182 (accept_3_2 25 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 182 2 12 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 182 2 11 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 182
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 182 2 10 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 182 (accept_3_2 19 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 182 2 9 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 182 2 8 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 182 2 7 60 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 182 (accept_3_2 13
  120 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 182 2 6 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 182
  (Polychromatic418967fa.accept_27_11_12_20_1_10509 11 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 182 2 5 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 120 182 (Polychromatic418967fa.accept_21_9_15_14_1_2790 9 120 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 182 2 4 60 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 182 (accept_3_2 7 120 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 182 2 3 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 182 2 2 60 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 182
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 182 2 1 60 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 182 (accept_3_2 1 120 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 119 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 119 182 7 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 119 182 (Polychromatic418967fa.accept_25_12_19_7_1_10508 62 119 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 182 (accept_3_2 61 119 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 182 (Polychromatic418967fa.accept_22_16_9_6_1_8804 60 119 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 182
  (Polychromatic418967fa.accept_22_15_9_6_1_10507 59 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 119 182 (accept_3_2 58 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 119 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 119 182 7 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 119 182 (accept_3_2 55 119 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 182 (Polychromatic418967fa.accept_19_16_5_11_1_4743 54 119 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 182 (accept_3_2 52 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 50 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 119 182 7 7 17 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 119 182
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 182 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 182 (accept_3_2 46 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 182 (accept_3_2 43 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  119 182 7 6 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 119 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 182 (accept_3_2 40 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 182 (Polychromatic418967fa.accept_22_16_9_6_1_8804 38 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 182 (accept_3_2 37 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 182
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 119 182 7 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 119 182 (accept_3_2 34 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 182 (accept_3_2 31 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 182 (Polychromatic418967fa.accept_22_8_9_6_1_8785 30 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 182 7 4 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 182 (Polychromatic418967fa.accept_22_4_9_6_1_3917 26 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 182 (accept_3_2 25 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 182
  (Polychromatic418967fa.accept_20_4_19_2_1_8971 24 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 182 (Polychromatic418967fa.accept_20_3_19_2_1_5926 23 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 182 (accept_3_2 22 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 119 182 7 3 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 119 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 182 (accept_3_2 19 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 119
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 182 (accept_3_2 16 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 119 182 7 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 119 182 (accept_3_2 13 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 182 (Polychromatic418967fa.accept_15_12_14_2_1_3794 12 119 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 182 (Polychromatic418967fa.accept_10_1_9_2_1_45
  11 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 182 (accept_3_2 10
  119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 119 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 119 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 182 7 1 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 182 (Polychromatic418967fa.accept_19_6_5_11_1_6067 6 119 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 182 (accept_3_2 4 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 182 (Polychromatic418967fa.accept_23_2_4_21_1_10506 2 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 182 (accept_3_2 1 119 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 118 182 (Eq.refl Bool.true) (allA_of_3_0 65 118 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 66 117 182 (Eq.refl Bool.true) (allA_succ_of_gcd 65 117 182 13 5 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 182 (accept_3_2 64 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 182
  (Polychromatic418967fa.accept_22_18_7_6_1_7109 62 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 182 (accept_3_2 61 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 182 (accept_3_2 58 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 182 (Polychromatic418967fa.accept_18_3_9_2_1_5053 57 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 182
  (Polychromatic418967fa.accept_11_1_7_6_1_378 56 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 182 (accept_3_2 55 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 117 182 13 4 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 117 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 182 (accept_3_2 49 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 182 (accept_3_2 46 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 182 (accept_3_2 43 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 117
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 182 (accept_3_2 40 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39
  117 182 13 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 117 182 (Polychromatic418967fa.accept_20_18_17_2_1_5941 38 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 117 182 (accept_3_2 37 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 117 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 182 (accept_3_2 34 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 182 (Polychromatic418967fa.accept_15_3_12_2_1_507
  33 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 182
  (Polychromatic418967fa.accept_19_13_3_11_1_4706 32 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 117 182 (accept_3_2 31 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 117 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 182 (accept_3_2 28 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 117 182 13 2 9 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 182 (accept_3_2 25
  117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 182 (accept_3_2 22 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 182
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 182 (accept_3_2 19 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 182 (accept_3_2 16 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 117 182 13 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 117 182 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 117 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 182 (accept_3_2 10 117 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 182 (Polychromatic418967fa.accept_10_9_7_2_1_887 9
  117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 182
  (Polychromatic418967fa.accept_19_8_3_11_1_6048 8 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 182 (accept_3_2 7 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 182 (accept_3_2 4 117 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 182
  (Polychromatic418967fa.accept_19_2_3_11_1_10505 2 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 182 (accept_3_2 1 117 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 116 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 116 182 2 33 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 182 2 32 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 182
  (Polychromatic418967fa.accept_25_13_16_7_1_10504 63 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 182 2 31 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 182 (accept_3_2 61 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 182 2 30 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 182 2 29 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 182 2 28 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 182 (accept_3_2 55 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 182 2 27 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 182 2 26 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 182 2 25 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 182 (accept_3_2 49 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 182 2 24 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 116 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 182 2 23 58 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 182
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 182 2 22 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 182 (accept_3_2 43 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 182 2 21 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 182 2 20 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 182 2 19 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 182 (accept_3_2 37 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 182 2 18 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 116 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 182 2 17 58 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 182 2 16 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 182 (accept_3_2 31 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 182 2 15 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 182 2 14 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 182
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 182 2 13 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 182 (accept_3_2 25 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 182 2 12 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 182 2 11 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 182 2 10 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 182 (accept_3_2 19 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 182 2 9 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 116 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 182 2 8 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 182 2 7 58 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 182 (accept_3_2 13
  116 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 182 2 6 58 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 182 2 5 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 182 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 116 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 182 2 4 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 182 (accept_3_2 7 116 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 182 2 3 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 116 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 182 2 2 58 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  116 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 182 2 1 58 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 182 (accept_3_2 1
  116 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 115 182 (Eq.refl Bool.true)
  (allA_of_3_0 68 115 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 114 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 114 182 2 34 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 182 (accept_3_2 67 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 182 2 33 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 182 (Polychromatic418967fa.accept_16_1_2_6_1_2295 65 114 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 182 2 32 57 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 182 2 31 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 182 (accept_3_2 61 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 182 2 30 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 182 2 29 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 182 2 28 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 182 (accept_3_2 55 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 182 2 27 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 182 2 26 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 182 2 25 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 182 (accept_3_2 49 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 182 2 24 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 182 2 23 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 182 2 22 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 182 (accept_3_2 43 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 182 2 21 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 182 2 20 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 182 2 19 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 182 (accept_3_2 37 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 182 2 18 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 182 2 17 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 182 2 16 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 182 (accept_3_2 31 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 182 2 15 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 182 (Polychromatic418967fa.accept_23_6_22_21_1_10503 29 114 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 182 2 14 57 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 182 2 13 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 182 (accept_3_2 25 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 182 2 12 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 182 2 11 57 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 182 2 10 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 182 (accept_3_2 19 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 182 2 9 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 114 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 182 2 8 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 182 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 182 2 7 57 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 182
  (accept_3_2 13 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 182 2 6 57 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 182
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 182 2 5 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 114 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 182 2 4 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 182 (accept_3_2 7 114 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 182 2 3 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 182 2 2 57 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  114 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 182 2 1 57 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 182 (accept_3_2 1
  114 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 113 182 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 113
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 182 (accept_3_2 67 113
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 113 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 65 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 182 (accept_3_2 64 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 182 (Polychromatic418967fa.accept_9_8_5_2_1_422
  62 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 182 (accept_3_2 61
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 182 (accept_3_2 58 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 182 (Polychromatic418967fa.accept_12_8_5_2_1_746
  56 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 182 (accept_3_2 55
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 182
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 113 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 182 (accept_3_2 52 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342
  50 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 182 (accept_3_2 49
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 182 (accept_3_2 46 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 182 (Polychromatic418967fa.accept_9_8_5_2_1_422
  44 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 182 (accept_3_2 43
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 182 (accept_3_2 40 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 182
  (Polychromatic418967fa.accept_20_18_13_2_1_10463 38 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 113 182 (accept_3_2 37 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 113 182 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 182 (accept_3_2 34 113 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 182 (accept_3_2 31 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 182 (Polychromatic418967fa.accept_19_10_18_11_1_10502 29 113 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 182 (accept_3_2 28 113 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 182 (accept_3_2 25 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 182 (accept_3_2 22 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 182
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 182 (accept_3_2 19 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 182 (accept_3_2 16 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 182
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 182 (accept_3_2 13 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 182 (accept_3_2 10 113 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 182 (accept_3_2 7 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 182 (accept_3_2 4 113 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 182
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 182 (accept_3_2 1 113 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 112 182 (Eq.refl Bool.true)
  (allA_of_3_0 71 112 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 111 182 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 182 (accept_3_2 70 111 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 182 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 182 (accept_3_2 67
  111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 182 (accept_3_2 64 111 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 182 (accept_3_2 61 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 182 (accept_3_2 58 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 182 (accept_3_2 55 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 111 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 182 (accept_3_2 52 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 182 (accept_3_2 49 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 182 (Polychromatic418967fa.accept_17_14_9_12_1_5350 48 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 182 (accept_3_2 46 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 182 (accept_3_2 43 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 182 (accept_3_2 40 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 182
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 182 (accept_3_2 37 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 182 (accept_3_2 34 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 182 (accept_3_2 31 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 182 (accept_3_2 28 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 182 (accept_3_2 25 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 182 (accept_3_2 22 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 182
  (Polychromatic418967fa.accept_21_20_6_14_1_5716 20 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 111 182 (accept_3_2 19 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 111 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 111 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 182 (accept_3_2 16 111 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431
  15 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 182 (accept_3_2 13 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 182 (accept_3_2 10 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 182 (accept_3_2 7 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 182 (accept_3_2 4 111 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 111 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 182
  (Polychromatic418967fa.accept_19_2_16_11_1_6045 2 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 182 (accept_3_2 1 111 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 110 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 110 182 2 36 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 182 2 35 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 182
  (Polychromatic418967fa.accept_31_7_17_27_1_10501 69 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 110 182 2 34 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 110 182 (accept_3_2 67 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 182 2 33 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 182 (Polychromatic418967fa.accept_20_5_10_2_1_7314 65 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 182 2 32 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 182
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 63 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 182 2 31 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 182 (accept_3_2 61 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 182 2 30 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 182 (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 182 2 29 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 182
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 57 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 182 2 28 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 182 (accept_3_2 55 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 182 2 27 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 182 (Polychromatic418967fa.accept_20_13_10_2_1_10500 53 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 182 2 26 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 182
  (Polychromatic418967fa.accept_21_9_5_14_1_1568 51 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 182 2 25 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 182 (accept_3_2 49 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 182 2 24 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 182 (Polychromatic418967fa.accept_19_9_15_11_1_7687 47 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 182 2 23 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 182
  (Polychromatic418967fa.accept_19_7_15_11_1_3420 45 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 182 2 22 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 182 (accept_3_2 43 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 182 2 21 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 182 2 20 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 182
  (Polychromatic418967fa.accept_17_5_8_12_1_6609 39 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 182 2 19 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 182 (accept_3_2 37 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 182 2 18 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 182 (Polychromatic418967fa.accept_19_16_15_11_1_7684 35 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 182 2 17 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 182
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 33 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 182 2 16 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 182 (accept_3_2 31 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 182 2 15 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 182 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 182 2 14 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 182
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 182 2 13 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 182 (accept_3_2 25 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 182 2 12 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 182 (Polychromatic418967fa.accept_19_4_15_11_1_7498 23 110 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 182 2 11 55 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 182
  (Polychromatic418967fa.accept_17_4_8_12_1_9165 21 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 182 2 10 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 182 (accept_3_2 19 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 182 2 9 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 182 (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 110 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 182 2 8 55 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 182
  (Polychromatic418967fa.accept_20_15_10_2_1_5924 15 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 110 182 2 7 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 110 182 (accept_3_2 13 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 182 2 6 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 110 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 110 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 182 2 5 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 182 (Polychromatic418967fa.accept_19_9_15_11_1_7687
  9 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 182 2 4 55 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 182 (accept_3_2 7
  110 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 182 2 3 55 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 110 182
  (Polychromatic418967fa.accept_17_5_8_12_1_6609 5 110 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 110 182 2 2 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 110 182 (Polychromatic418967fa.accept_15_3_5_2_1_2816 3 110 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 182 2 1 55 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 182 (accept_3_2 1 110 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 110 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  109 182 (Eq.refl Bool.true) (allA_of_3_0 74 109 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 108 182
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 182 2 37 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 182 (accept_3_2 73 108 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 108 182 2 36 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 108 182 (Polychromatic418967fa.accept_21_8_3_14_1_4165 71 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 182 2 35 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 182
  (Polychromatic418967fa.accept_11_3_9_6_1_105 69 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 182 2 34 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 182 (accept_3_2 67 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 182 2 33 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 108 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 182 2 32 54 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 182
  (Polychromatic418967fa.accept_19_6_13_11_1_7495 63 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 108 182 2 31 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 182 (accept_3_2 61 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 182 2 30 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 182 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 182 2 29 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 182
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 182 2 28 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 182 (accept_3_2 55 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 182 2 27 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 182 (Polychromatic418967fa.accept_17_2_6_12_1_7912 53 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 182 2 26 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 182
  (Polychromatic418967fa.accept_21_9_3_14_1_2806 51 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 182 2 25 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 182 (accept_3_2 49 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 182 2 24 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 108 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 182 2 23 54 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 182 2 22 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 182 (accept_3_2 43 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 182 2 21 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 182 (Polychromatic418967fa.accept_19_3_13_11_1_2220 41 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 182 2 20 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 182
  (Polychromatic418967fa.accept_28_11_24_14_1_10499 39 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 108 182 2 19 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 108 182 (accept_3_2 37 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 182 2 18 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 182 2 17 54 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 182
  (Polychromatic418967fa.accept_21_12_3_14_1_10498 33 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 108 182 2 16 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 108 182 (accept_3_2 31 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 182 2 15 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 182 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 182 2 14 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 182
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 182 2 13 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 182 (accept_3_2 25 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 182 2 12 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 182 (Polychromatic418967fa.accept_21_2_3_14_1_5690 23 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 182 2 11 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 182
  (Polychromatic418967fa.accept_19_2_13_11_1_10497 21 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 108 182 2 10 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 108 182 (accept_3_2 19 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 182 2 9 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 182 (Polychromatic418967fa.accept_19_17_13_11_1_2222 17 108 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 182 2 8 54 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 108 182 2 7 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 108 182 (accept_3_2 13 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  108 182 2 6 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 108 182 (Polychromatic418967fa.accept_17_11_6_12_1_5348 11 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 182 2 5 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 182 (Polychromatic418967fa.accept_21_9_3_14_1_2806 9 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 182 2 4 54 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 182 (accept_3_2 7 108 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 182 2 3 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 182 2 2 54 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 182
  (Polychromatic418967fa.accept_11_3_9_6_1_105 3 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 182 2 1 54 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 182 (accept_3_2 1 108 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 107 182 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 182 (Polychromatic418967fa.accept_10_4_7_2_1_211
  74 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 182 (accept_3_2 73
  107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 182
  (Polychromatic418967fa.accept_20_12_7_2_1_4448 72 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 182 (Polychromatic418967fa.accept_21_8_2_14_1_10496 71 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 182 (accept_3_2 70 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 182 (accept_3_2 67 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 182 (accept_3_2 64 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 182
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 62 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 182 (accept_3_2 61 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 182 (accept_3_2 58 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 182 (accept_3_2 55 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 182 (accept_3_2 52 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 182 (accept_3_2 49 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 182 (accept_3_2 46 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 182 (accept_3_2 43 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 182 (accept_3_2 40 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 182
  (Polychromatic418967fa.accept_20_18_7_2_1_4449 38 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 182 (accept_3_2 37 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 182 (accept_3_2 34 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 182 (accept_3_2 31 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 182 (accept_3_2 28 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 182
  (Polychromatic418967fa.accept_17_9_5_12_1_6606 26 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 182 (accept_3_2 25 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 182 (accept_3_2 22 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 182 (accept_3_2 19 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 182 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 182 (accept_3_2 16 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 182 (accept_3_2 13 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 182 (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 182 (accept_3_2 10 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 182 (accept_3_2 7 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 182 (accept_3_2 4 107 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 182
  (Polychromatic418967fa.accept_16_2_11_6_1_737 2 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 182 (accept_3_2 1 107 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 106 182 (Eq.refl
  Bool.true) (allA_of_3_0 77 106 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 105 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 105 182 7 11 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 105 182 (accept_3_2 76 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 182 (Polychromatic418967fa.accept_22_8_17_6_1_8769 74 105
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 182 (accept_3_2 73 105
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 182
  (Polychromatic418967fa.accept_19_15_10_11_1_4735 72 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 182 7 10 15 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 182
  (Polychromatic418967fa.accept_19_12_10_11_1_10495 69 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 182 (accept_3_2 67 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 182 (accept_3_2 64 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63
  105 182 7 9 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  62 105 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 182 (accept_3_2 61 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 105 182 (Polychromatic418967fa.accept_19_3_10_11_1_7669 60 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 182 (accept_3_2 58
  105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 105 182 7 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 105 182 (accept_3_2 55 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 182 (accept_3_2 52 105 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 105 182 7 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 105 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 182 (accept_3_2 46 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 182
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 45 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 105 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 182 (accept_3_2 43 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 105 182 7 6 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 105 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 182 (accept_3_2 40 105 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 182 (accept_3_2 37 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 182 (Polychromatic418967fa.accept_25_11_5_7_1_10494 36 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 105 182 7 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 105 182 (accept_3_2 34 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 182 (accept_3_2 31 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 182 (Polychromatic418967fa.accept_9_3_6_2_1_160
  30 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 105 182 7 4 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 182 (accept_3_2 25 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 182
  (Polychromatic418967fa.accept_17_7_3_12_1_4098 24 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 182 (accept_3_2 22 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 105 182 7 3 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 105 182 (Polychromatic418967fa.accept_19_1_10_11_1_4721 20 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 182 (accept_3_2 19 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 182 (Polychromatic418967fa.accept_10_8_5_2_1_881
  18 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 182 (accept_3_2 16 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 105 182 7 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 105 182 (accept_3_2 13 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 182 (accept_3_2 10 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 182 (Polychromatic418967fa.accept_25_9_5_7_1_10493
  9 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 182 7 1 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 182 (accept_3_2 4 105 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 182
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 182 (accept_3_2 1 105 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 104 182 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 104 182 26 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 182 2 38 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 182 2 37 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 182 (accept_3_2 73 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 182 2 36 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 182 2 35 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 182 2 34 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 182 (accept_3_2 67 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 182 2 33 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 104 182 13 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 104 182 2 32 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 104 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 104 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 182 2 31 52 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 182 (accept_3_2 61 104 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 182 2 30 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 104 182 2 29 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 104 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 104 182 2 28 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 104 182 (accept_3_2 55 104 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 104 182 2 27 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 104 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53
  104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 182 26 2 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 182 2 25 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 182 (accept_3_2 49 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 182 2 24 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 182 2 23 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 182
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 182 2 22 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 182 (accept_3_2 43 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 182 2 21 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 182 2 20 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 104 182 13 3 8 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 104 182 2 19 52 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 182 (accept_3_2 37 104 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 182 2 18 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 182 2 17 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 182 2 16 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 182 (accept_3_2 31 104 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 182 2 15 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 182 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 182 2 14 52 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 182 26 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 104 182 (accept_3_2 25 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  104 182 2 12 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 104 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 182 2 11 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 182 2 10 52 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 182 (accept_3_2 19
  104 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 182 2 9 52 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 182 2 8 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 104 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 182 2 7 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 104 182 13 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 104 182 2 6 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  11 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 182 2 5 52 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 182
  (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 182 2 4 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 182 (accept_3_2 7 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  182 2 3 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 182 2 2 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 182 2 1 52 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 182 (accept_3_2 1 104 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 103 182 (Eq.refl Bool.true) (allA_of_3_0 80 103 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 102 182 (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 182 2 40 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 182 (accept_3_2 79 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 182 2 39 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 77
  102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 182 2 38 51 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 182
  (Polychromatic418967fa.accept_11_9_3_6_1_797 75 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 182 2 37 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 182 (accept_3_2 73 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 182 2 36 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 182 2 35 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 182 2 34 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 182 (accept_3_2 67 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 182 2 33 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 182 2 32 51 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 182
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 182 2 31 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 182 (accept_3_2 61 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 182 2 30 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 182 2 29 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 182 2 28 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 182 (accept_3_2 55 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 182 2 27 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 182 2 26 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 182 2 25 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 182 (accept_3_2 49 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 182 2 24 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 182 (Polychromatic418967fa.accept_19_9_7_11_1_7602 47 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 182 2 23 51 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 182 2 22 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 182 (accept_3_2 43 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 182 2 21 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 182 2 20 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 182 2 19 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 182 (accept_3_2 37 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 182 2 18 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 182 2 17 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 182 2 16 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 182 (accept_3_2 31 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 182 2 15 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 182 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 182 2 14 51 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 182 2 13 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 182 (accept_3_2 25 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 182 2 12 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 182 2 11 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 182 2 10 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 182 (accept_3_2 19 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 182 2 9 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 182 2 8 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 182 2 7 51 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 182 (accept_3_2 13
  102 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 182 2 6 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 182
  (Polychromatic418967fa.accept_21_11_18_14_1_5646 11 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 102 182 2 5 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 102 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 182 2 4 51 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 182 (accept_3_2 7 102 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 182 2 3 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 182 2 2 51 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 102 182 2 1 51 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 182 (accept_3_2 1 102 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 101 182 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 101 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 182 (Polychromatic418967fa.accept_12_8_5_2_1_746
  80 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 182 (accept_3_2 79
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 182
  (Polychromatic418967fa.accept_21_15_17_14_1_4191 78 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 182 (Polychromatic418967fa.accept_19_1_6_11_1_7548 77 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 182 (accept_3_2 76 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 182
  (Polychromatic418967fa.accept_19_17_6_11_1_10492 74 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 101 182 (accept_3_2 73 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 101 182 (Polychromatic418967fa.accept_19_15_6_11_1_9047 72 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 182 (accept_3_2 70
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 101 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 182 (accept_3_2 67 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 101 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 182
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 182 (accept_3_2 64 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 182 (Polychromatic418967fa.accept_17_11_16_12_1_1984 62 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 182 (accept_3_2 61 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 182 (Polychromatic418967fa.accept_21_18_17_14_1_10491 60
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 182 (accept_3_2 58 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 182 (accept_3_2 55 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 182 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 101
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 182
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 182 (accept_3_2 52 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 182 (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 182 (accept_3_2 49 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 101
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 182 (accept_3_2 46 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 182 (accept_3_2 43 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 182 (Polychromatic418967fa.accept_22_20_13_6_1_10490 42
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 182
  (Polychromatic418967fa.accept_21_20_17_14_1_10489 41 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 101 182 (accept_3_2 40 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 182 (Polychromatic418967fa.accept_22_16_13_6_1_10488 38
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 182 (accept_3_2 37
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 182 (accept_3_2 34 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 101 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 182 (Polychromatic418967fa.accept_12_8_5_2_1_746
  32 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 182 (accept_3_2 31
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 182
  (Polychromatic418967fa.accept_17_13_16_12_1_6562 30 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 182 (accept_3_2 28 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 182 (accept_3_2 25 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 182 (Polychromatic418967fa.accept_15_9_11_2_1_1882 24 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 182 (accept_3_2 22 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 182 (accept_3_2 19 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 182 (Polychromatic418967fa.accept_17_1_16_12_1_5298 18 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 182 (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 182 (accept_3_2 16 101 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 182
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 101 182 (accept_3_2 13 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 101 182 (Polychromatic418967fa.accept_23_12_9_21_1_10487 12 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 182 (accept_3_2 10
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 101 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 182 (accept_3_2 7 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 101 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 101 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 182 (Polychromatic418967fa.accept_15_5_11_2_1_1095
  5 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 182 (accept_3_2 4
  101 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 101 182 (Polychromatic418967fa.accept_21_2_17_14_1_5644 2 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 182 (accept_3_2 1 101 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 101 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 100 182 (Eq.refl Bool.true) (allA_of_3_0 83 100 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 84 99 182 (Eq.refl Bool.true) (allA_succ_of_accept 83 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 182 (accept_3_2 82 99
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 182
  (Polychromatic418967fa.accept_21_17_15_14_1_5707 80 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 99 182 (accept_3_2 79 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 99 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 182 (accept_3_2 76 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 182 (Polychromatic418967fa.accept_16_11_3_6_1_4462
  75 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 182
  (Polychromatic418967fa.accept_19_17_4_11_1_4731 74 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 182 (accept_3_2 73 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 182 (Polychromatic418967fa.accept_19_15_4_11_1_7652 72 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 182 (accept_3_2 70 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 182 (accept_3_2 67 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 182 (accept_3_2 64 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 182 (Polychromatic418967fa.accept_20_3_19_2_1_5926 63 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 182
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 62 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 99 182 (accept_3_2 61 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 99 182 (Polychromatic418967fa.accept_17_9_14_12_1_9177 60 99 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 182 (accept_3_2 58 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 182
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 182 (accept_3_2 55 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 182 (accept_3_2 52 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 182 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 182
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 50 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 182 (accept_3_2 49 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 182 (Polychromatic418967fa.accept_22_4_11_6_1_10486 48 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 182 (accept_3_2 46 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 182
  (Polychromatic418967fa.accept_20_4_19_2_1_8971 44 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 182 (accept_3_2 43 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 182 (accept_3_2 40 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 182 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 182 (accept_3_2 37 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 182 (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 182 (accept_3_2 34 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 182
  (Polychromatic418967fa.accept_17_15_14_12_1_1973 32 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 182 (accept_3_2 31 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 182 (accept_3_2 28 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 182 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  27 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 182
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 182 (accept_3_2 25 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 182 (accept_3_2 22 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 182
  (Polychromatic418967fa.accept_16_4_3_6_1_6805 20 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 182 (accept_3_2 19 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 182 (accept_3_2 16 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 182 (Polychromatic418967fa.accept_17_15_14_12_1_1973 15 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 182
  (Polychromatic418967fa.accept_23_14_7_21_1_5233 14 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 182 (accept_3_2 13 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 182 (Polychromatic418967fa.accept_19_12_4_11_1_6078 12 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 182 (accept_3_2 10 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 182 (accept_3_2 7 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 182 (accept_3_2 4 99 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 182 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 99 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 2
  99 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 182 (accept_3_2 1 99 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 98 182 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 98 182 14 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 98 182 (Polychromatic418967fa.accept_16_3_2_6_1_4461 83 98 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 182 2 41 49 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 182
  (Polychromatic418967fa.accept_15_6_8_2_1_104 81 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 182 2 40 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 98 182 (accept_3_2 79 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 98
  182 2 39 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 98
  182 7 11 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 98
  182 2 38 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  98 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 98 182 2 37 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 98 182 (accept_3_2 73 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 182 2 36 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 98 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 71 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 182 14 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 98 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 182 2 34 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 182 (accept_3_2 67
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 182 2 33 49 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 65 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 98 182 2 32 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 98 182 7 9 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 98 182 2 31 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 98 182 (accept_3_2 61 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98
  182 2 30 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  98 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 98 182 2 29 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 98 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 98 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 182 14 4 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 182 (accept_3_2 55 98 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 182 2 27 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 182 (Polychromatic418967fa.accept_18_17_8_2_1_2622
  53 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 182 2 26 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 182 2 25 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 98 182 7 7 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 98 182 2 24 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 98 182 (Polychromatic418967fa.accept_19_9_3_11_1_7505 47 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 182 2 23 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 45
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 182 2 22 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 182 (accept_3_2 43
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 182 14 3 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 98 182 2 20 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 98 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 182 2 19 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 182 (accept_3_2 37 98 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 182 2 18 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 98 182 7 5 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 98 182 2 17 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 182 2 16 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 182 (accept_3_2 31
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 182 2 15 49 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 182
  (Polychromatic418967fa.accept_19_10_3_11_1_7587 29 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 182 14 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 182 2 13 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 182 (accept_3_2 25 98 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 182 2 12 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 182 2 11 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 98 182 7 3 14 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 98 182 2 10 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 182 (accept_3_2 19
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 182 2 9 49 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 182
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 98 182 2 8 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 98 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 182 14 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 182 (accept_3_2 13 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 98 182 2 6 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 98 182 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 98 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 182 2 5 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9
  98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 182 2 4 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 98 182 7 1 14 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 98 182 2 3 49 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 182 2 2 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 182 2 1 49 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 182 (accept_3_2 1 98 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 86 97 182 (Eq.refl Bool.true) (allA_of_3_0 86 97 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  87 96 182 (Eq.refl Bool.true) (allA_succ_of_gcd 86 96 182 2 43 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 96 182 (accept_3_2 85 96 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 96 182 2 42 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 96 182 (Polychromatic418967fa.accept_15_8_6_2_1_1128 83 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 182 2 41 48 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 96 182 2 40 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 96 182 (accept_3_2 79 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96
  182 2 39 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  96 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 96 182 2 38 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 96 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 182 2 37 48 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 182 (accept_3_2 73 96 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 182 2 36 48 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 182 2 35 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 96 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 69 96 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 182 2 34 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 182 (accept_3_2 67 96 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 182 2 33 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 182 (Polychromatic418967fa.accept_17_14_11_12_1_4109 65 96
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 182 2 32 48 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 182
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 63 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 182 2 31 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 96 182 (accept_3_2 61 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96
  182 2 30 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  96 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 96 182 2 29 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 96 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 182 2 28 48 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 182 (accept_3_2 55 96 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 182 2 27 48 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 182 2 26 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 96 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 96 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 182 2 25 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 182 (accept_3_2 49 96 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 182 2 24 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 96 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 182 2 23 48 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 182
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 45 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 182 2 22 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 182 (accept_3_2 43 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  182 2 21 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  96 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 182 2 20 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 96 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 182 2 19 48 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 182 (accept_3_2 37 96 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 182 2 18 48 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 182 2 17 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 96 182 (Polychromatic418967fa.accept_17_16_11_12_1_2008 33 96 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 182 2 16 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 182 (accept_3_2 31 96 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 182 2 15 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 182 (Polychromatic418967fa.accept_19_10_1_11_1_7532 29 96
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 182 2 14 48 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 182
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 182 2 13 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 182 (accept_3_2 25 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96
  182 2 12 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  96 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 96 182 2 11 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 96 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 182 2 10 48 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 182 (accept_3_2 19 96 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 182 2 9 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17
  96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 182 2 8 48 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 182
  (Polychromatic418967fa.accept_19_15_1_11_1_7503 15 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 182 2 7 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 182 (accept_3_2 13 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  182 2 6 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 182 2 5 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 182 (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 96 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 182 2 4 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 182 (accept_3_2 7 96 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 182 2 3 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 182 2 2 48 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 182 2 1 48 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 182 (accept_3_2 1 96 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 95 182
  (Eq.refl Bool.true) (allA_succ_of_accept 87 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 182
  (Polychromatic418967fa.accept_15_11_5_2_1_520 86 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 95 182 (accept_3_2 85 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  95 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 95 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 182 (accept_3_2 82 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 95 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 95 182 (accept_3_2 79 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  95 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 182 (accept_3_2 76 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 95 182
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 74 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 95 182 (accept_3_2 73 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  95 182 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 95 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 182 (accept_3_2 70 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 182 (accept_3_2 67 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 182 (accept_3_2 64 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 182 (accept_3_2 61 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  95 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 95 182 (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 182 (accept_3_2 58 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 182
  (Polychromatic418967fa.accept_11_1_7_6_1_378 56 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 95 182 (accept_3_2 55 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  95 182 (Polychromatic418967fa.accept_21_12_11_14_1_7239 54 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 182 (accept_3_2 52 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 182
  (Polychromatic418967fa.accept_20_10_15_2_1_3132 50 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 182 (accept_3_2 49 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 182 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 182 (accept_3_2 46 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 182 (accept_3_2 43 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 182 (accept_3_2 40 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 182 (accept_3_2 37 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 182 (Polychromatic418967fa.accept_17_2_10_12_1_7915 36 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 182 (accept_3_2 34 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 182 (accept_3_2 31 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 182 (accept_3_2 28 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 182 (accept_3_2 25 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 182 (accept_3_2 22 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 182 (accept_3_2 19 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 182 (accept_3_2 16 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 182
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 182 (accept_3_2 13 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 182 (accept_3_2 10 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 182 (accept_3_2 7 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 182 (accept_3_2 4 95 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 182 (Polychromatic418967fa.accept_17_2_10_12_1_7915
  2 95 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 182 (accept_3_2 1 95
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 94 182
  (Eq.refl Bool.true) (allA_of_3_0 89 94 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 93 182 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 182 (accept_3_2 88 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 182 (accept_3_2 85 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 182 (Polychromatic418967fa.accept_16_4_13_6_1_4417 84 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 182 (accept_3_2 82 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 182 (accept_3_2 79 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 182 (accept_3_2 76 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 182
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 182 (accept_3_2 73 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 182 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 182 (accept_3_2 70 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 182 (accept_3_2 67 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 182 (accept_3_2 64 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 182 (accept_3_2 61 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 182 (accept_3_2 58 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 182 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 182
  (Polychromatic418967fa.accept_11_1_5_6_1_397 56 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 182 (accept_3_2 55 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 182 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 182 (accept_3_2 52 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 182 (accept_3_2 49 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 182 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 182 (accept_3_2 46 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 182 (accept_3_2 43 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 182 (accept_3_2 40 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 182
  (Polychromatic418967fa.accept_17_4_8_12_1_9165 38 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 182 (accept_3_2 37 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 182 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 182 (accept_3_2 34 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 182 (accept_3_2 31 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 182 (accept_3_2 28 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 182 (accept_3_2 25 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 182 (accept_3_2 22 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 182
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 182 (accept_3_2 19 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 182 (accept_3_2 16 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 182 (accept_3_2 13 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 182 (accept_3_2 10 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 182 (Polychromatic418967fa.accept_16_9_13_6_1_2334 9 93 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 182 (accept_3_2 7 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 182 (accept_3_2 4 93 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 182 (Polychromatic418967fa.accept_21_2_9_14_1_4189
  2 93 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 182 (accept_3_2 1 93
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 92 182
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 92 182 2 45 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 92 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 92 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 92 182 2 44 46 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 92 182
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 87 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 92 182 2 43 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 92 182 (accept_3_2 85 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92
  182 2 42 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  92 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 92 182 2 41 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 92 182 (Polychromatic418967fa.accept_19_5_16_11_1_4727 81 92 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 182 2 40 46 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 182 (accept_3_2 79 92 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 182 2 39 46 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 77 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 92 182 2 38 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 92 182 (Polychromatic418967fa.accept_21_12_8_14_1_8862 75 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 92 182 2 37 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 92 182 (accept_3_2 73 92 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92 182 2 36 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 92 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 92 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 182 2 35 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 182
  (Polychromatic418967fa.accept_20_9_12_2_1_5935 69 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 182 2 34 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 92 182 (accept_3_2 67 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92
  182 2 33 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  92 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 92 182 2 32 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 92 182 (Polychromatic418967fa.accept_19_6_16_11_1_9041 63 92 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 182 2 31 46 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 182 (accept_3_2 61 92 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 182 2 30 46 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 92 182 2 29 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 92 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 182 2 28 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 182 (accept_3_2 55 92 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 182 2 27 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 92 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 182 2 26 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 182
  (Polychromatic418967fa.accept_19_13_16_11_1_6047 51 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 92 182 2 25 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 92 182 (accept_3_2 49 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 182 2 24 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 92 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 182 2 23 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 182 (Polychromatic418967fa.accept_21_3_8_14_1_8864
  45 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 182 2 22 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 182 (accept_3_2 43
  92 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 182 2 21 46 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 182 2 20 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 182 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 182 2 19 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 182 (accept_3_2 37 92 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 182 2 18 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 92 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 182 2 17 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 182
  (Polychromatic418967fa.accept_19_14_16_11_1_9054 33 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 92 182 2 16 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 92 182 (accept_3_2 31 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 182 2 15 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 92 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 182 2 14 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 182
  (Polychromatic418967fa.accept_19_8_16_11_1_10485 27 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 92 182 2 13 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 92 182 (accept_3_2 25 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 182 2 12 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 92 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 182 2 11 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 182 (Polychromatic418967fa.accept_17_4_7_12_1_6556
  21 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 182 2 10 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 182 (accept_3_2 19
  92 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 182 2 9 46 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 92 182 2 8 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 92 182 (Polychromatic418967fa.accept_19_15_16_11_1_7689 15 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 182 2 7 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 182 (accept_3_2 13 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 92 182 2 6 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 92 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 182 2 5 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 182 (Polychromatic418967fa.accept_20_9_12_2_1_5935 9
  92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 182 2 4 46 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 182 (accept_3_2 7 92
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 182 2 3 46 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 92 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 182 2 2 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 182 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 182 2 1 46 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 182 (accept_3_2 1 92 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 182
  (allA_of_3_0 91 91 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 182 (allA_succ_of_accept 89 90 182
  (Polychromatic418967fa.accept_22_1_2_6_1_5427 89 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 182 2 44 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 90 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 87 90 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 182 2 43 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 182 (accept_3_2 85 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 182 2 42 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 182 (Polychromatic418967fa.accept_19_7_14_11_1_4724 83 90
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 182 2 41 45 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 182
  (Polychromatic418967fa.accept_11_4_2_6_1_389 81 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 182 2 40 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 90 182 (accept_3_2 79 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90
  182 2 39 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  90 182 (Polychromatic418967fa.accept_17_9_5_12_1_6606 77 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 90 182 2 38 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 90 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 75 90 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 182 2 37 45 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 182 (accept_3_2 73 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 182 2 36 45 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 182
  (Polychromatic418967fa.accept_21_8_6_14_1_4184 71 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 90 182 2 35 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 90 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 182 2 34 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 182 (accept_3_2 67 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 182 2 33 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 182 (Polychromatic418967fa.accept_20_5_10_2_1_7314 65 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 182 2 32 45 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 182 2 31 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 182 (accept_3_2 61 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90
  182 2 30 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  90 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 90 182 2 29 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 90 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 90 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 182 2 28 45 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 182 (accept_3_2 55 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 182 2 27 45 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 182
  (Polychromatic418967fa.accept_19_15_14_11_1_7682 53 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 90 182 2 26 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 90 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 182 2 25 45 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 182 (accept_3_2 49 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 182 2 24 45 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 182
  (Polychromatic418967fa.accept_19_9_14_11_1_7496 47 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 182 2 23 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 90 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 90 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 182 2 22 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 182 (accept_3_2 43 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 182 2 21 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 182 (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 182 2 20 45 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 182 2 19 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 182 (accept_3_2 37 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90
  182 2 18 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  90 182 (Polychromatic418967fa.accept_19_16_14_11_1_4711 35 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 90 182 2 17 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 90 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 182 2 16 45 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 182 (accept_3_2 31 90 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 182 2 15 45 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 182
  (Polychromatic418967fa.accept_21_8_6_14_1_4184 29 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 182 2 14 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 90 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 182 2 13 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 182 (accept_3_2 25 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 182 2 12 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 182 (Polychromatic418967fa.accept_20_3_10_2_1_10484 23 90
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 182 2 11 45 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 182 2 10 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 182 (accept_3_2 19 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90
  182 2 9 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  90 182 (Polychromatic418967fa.accept_19_17_14_11_1_10483 17 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 182 2 8 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 182 2 7 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 182 (accept_3_2 13 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 182 2 6 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 182 (Polychromatic418967fa.accept_21_11_6_14_1_10482 11 90 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 182 2 5 45 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 182 2 4 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 182 (accept_3_2 7 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 182
  2 3 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90
  182 (Polychromatic418967fa.accept_19_5_14_11_1_6084 5 90 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 182 2 2 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 182 2 1 45 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 182 (accept_3_2 1 90 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 182
  (allA_succ_of_accept 88 89 182 (accept_3_2 88 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 182 (accept_3_2 85 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 182 (accept_3_2 82 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 80 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 182 (accept_3_2 79 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 182 (accept_3_2 76 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 182 (Polychromatic418967fa.accept_19_17_13_11_1_2222 74 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 182 (accept_3_2 73 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 182 (Polychromatic418967fa.accept_15_12_14_2_1_3794 72 89
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 182 (accept_3_2 70 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 182 (accept_3_2 67 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 182
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 182 (accept_3_2 64 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 62 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 182 (accept_3_2 61 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 182 (accept_3_2 58 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 182 (accept_3_2 55 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 182 (Polychromatic418967fa.accept_19_16_13_11_1_7679 54 89 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 182
  (Polychromatic418967fa.accept_17_2_4_12_1_6587 53 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 182 (accept_3_2 52 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 182 (accept_3_2 49 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 182 (accept_3_2 46 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 182 (accept_3_2 43 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 182 (accept_3_2 40 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 38 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 182 (accept_3_2 37 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 182 (Polychromatic418967fa.accept_17_2_4_12_1_6587 36 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 182 (accept_3_2 34 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 182 (accept_3_2 31 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 182
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 182 (accept_3_2 28 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 182 (Polychromatic418967fa.accept_17_9_4_12_1_2958 26 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 182 (accept_3_2 25 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 182 (accept_3_2 22 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 182 (accept_3_2 19 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 182
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 182 (accept_3_2 16 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 182 (accept_3_2 13 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 182 (accept_3_2 10 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 182 (accept_3_2 7 89 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 182 (accept_3_2 4 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 89 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 182 (accept_3_2 1 89 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 182 (allA_of_3_0 88 88 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 182
  (allA_succ_of_accept 86 87 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 87 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 182 (accept_3_2 85 87 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 182 (accept_3_2 82 87
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 80 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 182 (accept_3_2 79 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 182 (accept_3_2 76 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 74 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 182 (accept_3_2 73 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 182 (Polychromatic418967fa.accept_17_4_2_12_1_6554 72 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 182 (accept_3_2 70 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 182 (accept_3_2 67 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 182 (accept_3_2 64 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 182 (accept_3_2 61 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 182 (accept_3_2 58 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 182
  (Polychromatic418967fa.accept_27_2_6_20_1_10481 56 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 182 (accept_3_2 55 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 182 (accept_3_2 52 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 182 (accept_3_2 49 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 182 (accept_3_2 46 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 182 (accept_3_2 43 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 182 (accept_3_2 40 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 182
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 182 (accept_3_2 37 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 182 (accept_3_2 34 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 182 (accept_3_2 31 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 182 (accept_3_2 28 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 182 (accept_3_2 25 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 182 (accept_3_2 22 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 182
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 182 (accept_3_2 19 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 182 (accept_3_2 16 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 182 (accept_3_2 13 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 182 (accept_3_2 10 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 182 (accept_3_2 7 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 182 (accept_3_2 4 87 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 182 (Polychromatic418967fa.accept_21_2_3_14_1_5690
  2 87 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 182 (accept_3_2 1 87
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 182
  (allA_succ_of_accept 85 86 182 (accept_3_2 85 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  182 2 42 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  86 182 (Polychromatic418967fa.accept_17_15_1_12_1_7910 83 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 182 2 41 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 81 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 182 2 40 43 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 182 (accept_3_2 79 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 182 2 39 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 182
  (Polychromatic418967fa.accept_19_1_10_11_1_4721 77 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 182 2 38 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 86 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 86 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 182 2 37 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 182 (accept_3_2 73 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 182 2 36 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 182 2 35 43 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 182 2 34 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 86 182 (accept_3_2 67 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86
  182 2 33 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  86 182 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 86 182 2 32 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 182 (Polychromatic418967fa.accept_22_19_20_6_1_8814 63 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 182 2 31 43 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 182 (accept_3_2 61 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 182 2 30 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 182
  (Polychromatic418967fa.accept_19_2_10_11_1_7616 59 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 182 2 29 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 86 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 182 2 28 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 182 (accept_3_2 55 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 182 2 27 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 182 2 26 43 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 182 2 25 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 182 (accept_3_2 49 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  182 2 24 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 182 2 23 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 182 (Polychromatic418967fa.accept_21_3_2_14_1_7235 45 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 182 2 22 43 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 182 (accept_3_2 43 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 182 2 21 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 182 2 20 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 86 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 182 2 19 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 182 (accept_3_2 37 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 182 2 18 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 182 2 17 43 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 182 2 16 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 182 (accept_3_2 31 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  182 2 15 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 182 (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 182 2 14 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 182 (Polychromatic418967fa.accept_19_8_10_11_1_7614 27 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 182 2 13 43 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 182 (accept_3_2 25 86 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 182 2 12 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 182
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 23 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 182 2 11 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 182 2 10 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 182 (accept_3_2 19 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 182 2 9 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 182 2 8 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 182 2 7 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 182 (accept_3_2 13 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  182 2 6 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 182 2 5 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 182 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 182 2 4 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 182 (accept_3_2 7 86 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 182 2 3 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 182 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 86 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 182 2 2 43 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 182 2 1 43 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 182 (accept_3_2 1 86 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 182
  (allA_of_3_0 85 85 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 182 (allA_succ_of_accept 83 84 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 83 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 182 2 41 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 84 182 (Polychromatic418967fa.accept_17_13_16_12_1_6562 81 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 182 2 40 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 182 (accept_3_2 79 84 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 182 2 39 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 182 7 11 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 84 182 2 38 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 182 (Polychromatic418967fa.accept_16_11_4_6_1_4422 75 84 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 84 182 2 37 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 182 (accept_3_2 73
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 182 2 36 42 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 84 182 14 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 84 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 182 2 34 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 182 (accept_3_2 67 84 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 182 2 33 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 182 (Polychromatic418967fa.accept_20_5_4_2_1_5912 65 84 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 182 2 32 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 182 7 9 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 182 2 31 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 182 (accept_3_2 61
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 182 2 30 42 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 182 2 29 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 84 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 182 14 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 182 (accept_3_2 55 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 84 182 2 27 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 84 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 182 2 26 42 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 182 2 25 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 84 182 7 7 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 84 182 2 24 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 182 2 23 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 182 (Polychromatic418967fa.accept_11_1_7_6_1_378 45
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 182 2 22 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 182 (accept_3_2 43
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 182 14 3 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 182 2 20 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 182 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 182 2 19 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 182 (accept_3_2 37 84 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 182 2 18 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 182 7 5 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 182 2 17 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 182 2 16 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 182 (accept_3_2 31
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 182 2 15 42 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 182
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 29 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 182 14 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 182 2 13 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 182 (accept_3_2 25 84 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 182 2 12 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 182 2 11 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 182 7 3 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 182 2 10 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 182 (accept_3_2 19
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 182 2 9 42 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 182 2 8 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 182 14 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 182 (accept_3_2 13 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 84 182 2 6 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 84 182 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 84 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 182 2 5 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 182 (Polychromatic418967fa.accept_19_9_8_11_1_6072 9
  84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 182 2 4 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 182 7 1 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 182 2 3 42 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 182 2 2 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 182 (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 182 2 1 42 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 182 (accept_3_2 1 84 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 182 (allA_succ_of_accept 82 83 182 (accept_3_2 82 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 182 (accept_3_2 79 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 182 (Polychromatic418967fa.accept_20_18_3_2_1_5929
  78 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 182 (accept_3_2 76 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 182 (Polychromatic418967fa.accept_21_11_20_14_1_4179 74 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 182 (accept_3_2 73 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 182 (Polychromatic418967fa.accept_19_15_7_11_1_7657 72 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 182
  (Polychromatic418967fa.accept_10_1_3_2_1_220 71 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 182 (accept_3_2 70 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 182 (accept_3_2 67 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 182 (Polychromatic418967fa.accept_15_6_8_2_1_104 66 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 182 (accept_3_2 64 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 182 (Polychromatic418967fa.accept_23_16_14_21_1_10480 62 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 182 (accept_3_2 61 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 182 (Polychromatic418967fa.accept_21_18_20_14_1_5711 60 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 182
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 59 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 182 (accept_3_2 58 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 182 (accept_3_2 55 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 182 (accept_3_2 52 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 50 83 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 182 (accept_3_2 49 83 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 182 (Polychromatic418967fa.accept_17_14_15_12_1_1921 48 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 182
  (Polychromatic418967fa.accept_19_9_7_11_1_7602 47 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 182 (accept_3_2 46 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 182 (accept_3_2 43 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 182 (Polychromatic418967fa.accept_19_4_7_11_1_6056 42 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 182 (accept_3_2 40 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 182 (Polychromatic418967fa.accept_20_18_3_2_1_5929 38 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 182 (accept_3_2 37 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 182 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 182
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 182 (accept_3_2 34 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 182 (accept_3_2 31 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 182 (Polychromatic418967fa.accept_20_10_3_2_1_4444 30 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 182 (accept_3_2 28 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 182 (Polychromatic418967fa.accept_21_5_20_14_1_4162 26 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 182 (accept_3_2 25 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 182
  (Polychromatic418967fa.accept_19_4_7_11_1_6056 23 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 182 (accept_3_2 22 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 182 (accept_3_2 19 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 182 (accept_3_2 16 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 182 (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 182 (accept_3_2 13 83 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 182 (Polychromatic418967fa.accept_19_12_7_11_1_7658 12 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 182
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 182 (accept_3_2 10 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 83 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 182 (accept_3_2 7 83 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 182 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 83 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 182 (accept_3_2 4 83 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 182
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 182 (accept_3_2 1 83 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 182 (allA_of_3_0
  82 82 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 182 (allA_succ_of_accept 80 81 182
  (Polychromatic418967fa.accept_21_17_18_14_1_4138 80 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 81 182 (accept_3_2 79 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 81 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 81 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 182 (accept_3_2 76 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75
  81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 182
  (Polychromatic418967fa.accept_19_17_5_11_1_7509 74 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 182 (accept_3_2 73 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 182 (accept_3_2 70 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 182
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 182 (accept_3_2 67 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 182 (accept_3_2 64 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 182
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 62 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 81 182 (accept_3_2 61 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 81 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 81 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 182 (accept_3_2 58 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  57 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 182 (accept_3_2 55 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 182 (accept_3_2 52 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 182
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 182 (accept_3_2 49 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 182 (Polychromatic418967fa.accept_19_10_5_11_1_7597 48 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 182 (accept_3_2 46 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 182 (Polychromatic418967fa.accept_17_11_13_12_1_1968 45 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 182
  (Polychromatic418967fa.accept_19_6_5_11_1_6067 44 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 182 (accept_3_2 43 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 182 (accept_3_2 40 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 182 (accept_3_2 37 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 182 (accept_3_2 34 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 182
  (Polychromatic418967fa.accept_19_13_5_11_1_7653 32 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 182 (accept_3_2 31 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 182 (accept_3_2 28 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 182 (accept_3_2 25 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 182 (accept_3_2 22 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 182 (Polychromatic418967fa.accept_16_5_1_6_1_3367 21 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 182
  (Polychromatic418967fa.accept_21_20_18_14_1_10455 20 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 81 182 (accept_3_2 19 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 81 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 182 (accept_3_2 16 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 182
  (Polychromatic418967fa.accept_19_14_5_11_1_7712 14 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 182 (accept_3_2 13 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 182 (accept_3_2 10 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 182 (accept_3_2 7 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  182 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 182 (accept_3_2 4 81 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2
  81 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 182 (accept_3_2 1 81 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 182
  (allA_succ_of_accept 79 80 182 (accept_3_2 79 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  182 2 39 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 182 2 38 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 80 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 182 2 37 40 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 182 (accept_3_2 73 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 182 2 36 40 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 182 2 35 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 80 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 182 2 34 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 182 (accept_3_2 67 80 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 182 2 33 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 182 2 32 40 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 182
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 182 2 31 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 182 (accept_3_2 61 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  182 2 30 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 182 2 29 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 80 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 182 2 28 40 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 182 (accept_3_2 55 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 182 2 27 40 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 182
  (Polychromatic418967fa.accept_11_9_3_6_1_797 53 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 182 2 26 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 80 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 182 2 25 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 182 (accept_3_2 49 80 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 182 2 24 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 182 2 23 40 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 182
  (Polychromatic418967fa.accept_19_7_4_11_1_3414 45 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 182 2 22 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 182 (accept_3_2 43 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  182 2 21 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 182 2 20 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 80 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 182 2 19 40 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 182 (accept_3_2 37 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 182 2 18 40 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 80 182 2 17 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 80 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 80 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 182 2 16 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 182 (accept_3_2 31 80 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 182 2 15 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 182 2 14 40 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 182
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 182 2 13 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 80 182 (accept_3_2 25 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80
  182 2 12 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  80 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 80 182 2 11 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 80 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 182 2 10 40 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 182 (accept_3_2 19 80 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 182 2 9 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 17
  80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 182 2 8 40 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 182 2 7 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 182 (accept_3_2 13 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  182 2 6 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 182 2 5 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 80 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 182 2 4 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 182 (accept_3_2 7 80 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 182 2 3 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 182 2 2 40 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 182 2 1 40 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 182 (accept_3_2 1 80 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 182 (allA_of_3_0 79
  79 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 182 (allA_succ_of_accept 77 78 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 78 182 2 38 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 78 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 182 2 37 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 182 (accept_3_2 73 78 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 182 2 36 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 182 2 35 39 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 182 2 34 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 182 (accept_3_2 67 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78
  182 2 33 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 78
  182 13 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 78
  182 2 32 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  78 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 78 182 2 31 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 78 182 (accept_3_2 61 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 182 2 30 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 182 2 29 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 57
  78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 182 2 28 39 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 182 (accept_3_2 55
  78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 182 2 27 39 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 182 26 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 182 2 25 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 182 (accept_3_2 49 78 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 182 2 24 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 182 (Polychromatic418967fa.accept_19_9_2_11_1_7581 47 78 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 182 2 23 39 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 182 2 22 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 182 (accept_3_2 43 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  182 2 21 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 182 2 20 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 182 13 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 182 2 19 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 182 (accept_3_2 37 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 182 2 18 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 182 2 17 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273
  33 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 182 2 16 39 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 182 (accept_3_2 31
  78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 182 2 15 39 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 182
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 182 2 14 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 78 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 182 26 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 182 (accept_3_2 25 78 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 78 182 2 12 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 78 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 182 2 11 39 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 182 2 10 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 182 (accept_3_2 19 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78
  182 2 9 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  78 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 182 2 8 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 182 2 7 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 78 182 13 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 182 2 6 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 182
  (Polychromatic418967fa.accept_23_11_9_21_1_10479 11 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 182 2 5 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 78 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 182 2 4 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 182 (accept_3_2 7 78 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 182 2 3 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 182 2 2 39 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 182 2 1 39 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 182 (accept_3_2 1 78 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 182
  (allA_succ_of_accept 76 77 182 (accept_3_2 76 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 182 (accept_3_2 73 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 182 (Polychromatic418967fa.accept_17_4_9_12_1_9167 72 77 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 182 7 10 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 182 (accept_3_2 67 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 66
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 182
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 182 (accept_3_2 64 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  182 7 9 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 182 (accept_3_2 61 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 182 (accept_3_2 58 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 57
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 182 7 8 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 182 (accept_3_2 55
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 182 (accept_3_2 52 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 182
  (Polychromatic418967fa.accept_19_12_1_11_1_7538 50 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 77 182 7 7 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 77 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 182 (accept_3_2 46 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 182 (accept_3_2 43 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77
  182 7 6 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  77 182 (Polychromatic418967fa.accept_16_9_13_6_1_2334 41 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 182 (accept_3_2 40 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 182 (Polychromatic418967fa.accept_17_4_9_12_1_9167 38 77
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 182 (accept_3_2 37 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 182 (Polychromatic418967fa.accept_16_4_13_6_1_4417
  36 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 182 7 5 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 182 (accept_3_2 34
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 77 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 182 (accept_3_2 31 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 77 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 182 (Polychromatic418967fa.accept_10_9_7_2_1_887
  29 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 182 7 4 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 77 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 182 (accept_3_2 25 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 77 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 182 (accept_3_2 22 77
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 182 7 3 11 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 77 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 182 (accept_3_2 19 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 182 (Polychromatic418967fa.accept_19_18_1_11_1_10478 18 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 182 (accept_3_2 16 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 182 7 2 11 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 182 (accept_3_2 13 77 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 182 (accept_3_2 10 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 182 7 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 182
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 182 (accept_3_2 4 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 182 (Polychromatic418967fa.accept_22_2_11_6_1_10477 2 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 182 (accept_3_2 1 77 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 182 (allA_of_3_0 76 76 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 182 (allA_succ_of_accept 74 75
  182 (Polychromatic418967fa.accept_19_17_18_11_1_2215 74 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 182 (accept_3_2 73 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 182 (Polychromatic418967fa.accept_17_4_7_12_1_6556 72 75 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 182 (accept_3_2 70 75 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69
  75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 182 (accept_3_2 67 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 182 (accept_3_2 64 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 182 (accept_3_2 61 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 182 (accept_3_2 58 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 182
  (Polychromatic418967fa.accept_17_5_7_12_1_1951 56 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 182 (accept_3_2 55 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 182 (accept_3_2 52 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 182 (accept_3_2 49 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 182 (accept_3_2 46 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 182 (accept_3_2 43 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 182 (accept_3_2 40 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 182 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 182 (accept_3_2 37 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 182 (accept_3_2 34 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 182 (accept_3_2 31 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 182 (accept_3_2 28 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 182 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 182 (accept_3_2 25 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 182 (accept_3_2 22 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 182
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 20 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 182 (accept_3_2 19 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 182 (accept_3_2 16 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 182 (accept_3_2 13 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 182 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 182 (accept_3_2 10 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 182 (accept_3_2 7 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 182 (accept_3_2 4 75 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 182 (Polychromatic418967fa.accept_16_2_11_6_1_737 2
  75 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 182 (accept_3_2 1 75 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 182 (allA_succ_of_accept
  73 74 182 (accept_3_2 73 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 182 2 36 37 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 182
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 71 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 74 182 2 35 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 74 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 69 74 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 182 2 34 37 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 182 (accept_3_2 67 74 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 182 2 33 37 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 182
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 74 182 2 32 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 74 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 74 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 182 2 31 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 182 (accept_3_2 61 74 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 182 2 30 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 182 (Polychromatic418967fa.accept_22_15_8_6_1_8760 59 74 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 182 2 29 37 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 182 2 28 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 74 182 (accept_3_2 55 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74
  182 2 27 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  74 182 (Polychromatic418967fa.accept_17_2_6_12_1_7912 53 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 74 182 2 26 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 74 182 (Polychromatic418967fa.accept_19_13_17_11_1_4716 51 74 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 182 2 25 37 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 182 (accept_3_2 49 74 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 182 2 24 37 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 182 2 23 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 182 (Polychromatic418967fa.accept_17_11_6_12_1_5348 45 74 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 182 2 22 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 182 (accept_3_2 43 74 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 182 2 21 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 182 (Polychromatic418967fa.accept_21_20_11_14_1_5718 41 74
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 182 2 20 37 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 182
  (Polychromatic418967fa.accept_21_18_11_14_1_8846 39 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 74 182 2 19 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 74 182 (accept_3_2 37 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 182 2 18 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 74 182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 74 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 182 2 17 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888
  33 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 182 2 16 37 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 182 (accept_3_2 31
  74 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 182 2 15 37 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 182
  (Polychromatic418967fa.accept_21_8_11_14_1_5665 29 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 182 2 14 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 182 2 13 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 182 (accept_3_2 25 74 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 182 2 12 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 182 (Polychromatic418967fa.accept_19_4_17_11_1_7527 23 74
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 182 2 11 37 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 182
  (Polychromatic418967fa.accept_28_21_18_14_1_10476 21 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 74 182 2 10 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 74 182 (accept_3_2 19 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 182 2 9 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 74 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 182 2 8 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 182 (Polychromatic418967fa.accept_22_15_8_6_1_8760 15 74 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 182 2 7 37 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 182 (accept_3_2 13 74 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 182 2 6 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 182 (Polychromatic418967fa.accept_17_11_6_12_1_5348
  11 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 182 2 5 37 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 182
  (Polychromatic418967fa.accept_19_9_17_11_1_2226 9 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 182 2 4 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 182 (accept_3_2 7 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 182
  2 3 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 74 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 74 182 2 2 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 74 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 74 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 182 2 1 37 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 182 (accept_3_2 1 74 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 74 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 73 182 (allA_of_3_0 73 73 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 182
  (allA_succ_of_accept 71 72 182 (Polychromatic418967fa.accept_19_14_15_11_1_4739 71 72 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 182 2 35 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 182 (Polychromatic418967fa.accept_20_9_12_2_1_5935
  69 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 182 2 34 36 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 182 (accept_3_2 67
  72 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 182 2 33 36 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 182
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 182 2 32 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 72 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 72 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 182 2 31 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 182 (accept_3_2 61 72 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 182 2 30 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 182 (Polychromatic418967fa.accept_15_14_12_2_1_3804 59 72
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 182 2 29 36 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 182
  (Polychromatic418967fa.accept_20_17_12_2_1_8956 57 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 182 2 28 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 72 182 (accept_3_2 55 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72
  182 2 27 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  72 182 (Polychromatic418967fa.accept_17_2_4_12_1_6587 53 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 72 182 2 26 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 72 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 72 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 182 2 25 36 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 182 (accept_3_2 49 72 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 182 2 24 36 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 182
  (Polychromatic418967fa.accept_19_9_15_11_1_7687 47 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 182 2 23 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 72 182 (Polychromatic418967fa.accept_19_7_15_11_1_3420 45 72 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 182 2 22 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 182 (accept_3_2 43 72 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 182 2 21 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 182 (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 72 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 182 2 20 36 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 182
  (Polychromatic418967fa.accept_19_1_15_11_1_4712 39 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 72 182 2 19 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 72 182 (accept_3_2 37 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72
  182 2 18 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  72 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 72 182 2 17 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 72 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 182 2 16 36 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 182 (accept_3_2 31 72 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 182 2 15 36 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 182
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 182 2 14 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 72 182 (Polychromatic418967fa.accept_20_7_12_2_1_4465 27 72 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 182 2 13 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 182 (accept_3_2 25 72 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 182 2 12 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 182 (Polychromatic418967fa.accept_19_4_15_11_1_7498 23 72
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 182 2 11 36 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 182
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 182 2 10 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 182 (accept_3_2 19 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  182 2 9 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 182 (Polychromatic418967fa.accept_20_17_12_2_1_8956 17 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 182 2 8 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 182 (Polychromatic418967fa.accept_21_15_9_14_1_10462 15 72 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 182 2 7 36 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 182 (accept_3_2 13 72 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 182 2 6 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 182 (Polychromatic418967fa.accept_25_11_22_7_1_10475 11 72
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 182 2 5 36 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 182
  (Polychromatic418967fa.accept_17_9_4_12_1_2958 9 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 182 2 4 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 182 (accept_3_2 7 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 182
  2 3 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 72 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 182 2 2 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 72 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 182 2 1 36 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 182 (accept_3_2 1 72 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 182 (allA_succ_of_accept 70 71 182 (accept_3_2 70 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 182 (accept_3_2 67 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 66
  71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 182 (accept_3_2 64 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 182 (Polychromatic418967fa.accept_18_8_17_2_1_1557 62 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 182 (accept_3_2 61 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 182 (accept_3_2 58 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 182 (accept_3_2 55 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 182 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 182 (accept_3_2 52 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 182 (accept_3_2 49 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 182
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 47 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 182 (accept_3_2 46 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 182 (accept_3_2 43 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 182 (accept_3_2 40 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 182 (Polychromatic418967fa.accept_21_17_8_14_1_5638 38 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 182 (accept_3_2 37 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 182
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 182 (accept_3_2 34 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 182 (accept_3_2 31 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 182 (accept_3_2 28 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 182 (accept_3_2 25 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 182 (accept_3_2 22 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 182 (accept_3_2 19 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 182 (Polychromatic418967fa.accept_27_18_17_20_1_10474 18 71
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 182 (accept_3_2 16 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 182 (accept_3_2 13 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 182
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 182 (accept_3_2 10 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 182 (accept_3_2 7 71 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 182 (accept_3_2 4 71 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 182
  (Polychromatic418967fa.accept_21_2_8_14_1_4148 2 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 182 (accept_3_2 1 71 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 182 (allA_of_3_0 70 70 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 182 (allA_succ_of_accept 68 69 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 182 (accept_3_2 67 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 182 (accept_3_2 64 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 182 (accept_3_2 61 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 182 (Polychromatic418967fa.accept_19_3_12_11_1_7619 60 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 182 (accept_3_2 58 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 182
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 182 (accept_3_2 55 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 182 (accept_3_2 52 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 182 (accept_3_2 49 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 182 (accept_3_2 46 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 182 (Polychromatic418967fa.accept_19_7_12_11_1_7621 45 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 182 (accept_3_2 43 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 182 (accept_3_2 40 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 182 (accept_3_2 37 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 182 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 182 (accept_3_2 34 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 182 (Polychromatic418967fa.accept_16_1_5_6_1_4435 33 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 182 (accept_3_2 31 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 182 (accept_3_2 28 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 182 (accept_3_2 25 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 182 (Polychromatic418967fa.accept_19_5_12_11_1_10460 24 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 182 (accept_3_2 22 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 182
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 182 (accept_3_2 19 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 182 (accept_3_2 16 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 182 (accept_3_2 13 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 182 (accept_3_2 10 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 69 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 182 (accept_3_2 7 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 182 (accept_3_2 4 69 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 182 (Polychromatic418967fa.accept_21_2_6_14_1_1569
  2 69 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 182 (accept_3_2 1 69
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 182 (allA_succ_of_accept 67 68
  182 (accept_3_2 67 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 182 2 33 34 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 65 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 182 2 32 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 182 (Polychromatic418967fa.accept_22_19_2_6_1_10473 63 68 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 182 2 31 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 182 (accept_3_2 61 68 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 182 2 30 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 68 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 182 2 29 34 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 182 2 28 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 182 (accept_3_2 55 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  182 2 27 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 182 2 26 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 68 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 182 2 25 34 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 182 (accept_3_2 49 68 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 182 2 24 34 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 182 2 23 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 182 2 22 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 182 (accept_3_2 43 68 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 182 2 21 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 182 2 20 34 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 182 2 19 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 182 (accept_3_2 37 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  182 2 18 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 182 2 17 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 182 2 16 34 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 182 (accept_3_2 31 68 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 182 2 15 34 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 182 2 14 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 182 (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 68 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 182 2 13 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 182 (accept_3_2 25 68 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 182 2 12 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 68 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 182 2 11 34 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 182 2 10 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 182 (accept_3_2 19 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  182 2 9 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 182 2 8 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 68 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 182 2 7 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 182 (accept_3_2 13 68 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 182 2 6 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 68 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 182 2 5 34 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 182
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 182 2 4 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 182 (accept_3_2 7 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 182
  2 3 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 182 2 2 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 68 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 182 2 1 34 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 182 (accept_3_2 1 68 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 182
  (allA_of_3_0 67 67 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 182 (allA_succ_of_accept 65 66 182
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 65 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 182 2 32 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 182 2 31 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 182 (accept_3_2 61 66 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 182 2 30 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 182 2 29 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 182 2 28 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 182 (accept_3_2 55 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  182 2 27 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 182 2 26 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 182 2 25 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 182 (accept_3_2 49 66 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 182 2 24 33 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 182
  (Polychromatic418967fa.accept_23_1_20_21_1_10472 47 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 66 182 2 23 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 66 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 182 2 22 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 182 (accept_3_2 43 66 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 182 2 21 33 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 182 2 20 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 66 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 182 2 19 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 182 (accept_3_2 37 66 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 182 2 18 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 182 2 17 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 182 2 16 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 182 (accept_3_2 31 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66
  182 2 15 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  66 182 (Polychromatic418967fa.accept_21_8_3_14_1_4165 29 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 66 182 2 14 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 66 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 182 2 13 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 182 (accept_3_2 25 66 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 182 2 12 33 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 182 2 11 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 182 2 10 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 182 (accept_3_2 19 66 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 182 2 9 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 66 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 182 2 8 33 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 182 2 7 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 182 (accept_3_2 13 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  182 2 6 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  66 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 66 182 2 5 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 66 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 66 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 182 2 4 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 182 (accept_3_2 7 66 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 182 2 3 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 66 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 182 2 2 33 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 182 2 1 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 182 (accept_3_2 1 66 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 182 (allA_succ_of_accept 64 65 182
  (accept_3_2 64 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 182 (Polychromatic418967fa.accept_17_11_14_12_1_2995 62 65 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 182 (accept_3_2 61 65 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 182 (accept_3_2 58 65
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 182 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 182 (accept_3_2 55 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 182 (Polychromatic418967fa.accept_19_16_8_11_1_6080 54 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 65 182 13 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 182
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 182 (accept_3_2 49 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 182 (accept_3_2 46 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 182 (accept_3_2 43 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 182 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 182 (accept_3_2 40 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 39 65 182 13 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 65 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 182 (accept_3_2 37 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 182 (Polychromatic418967fa.accept_19_17_8_11_1_7605 36 65
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 182 (accept_3_2 34 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 182 (accept_3_2 31 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 182 (Polychromatic418967fa.accept_20_10_5_2_1_3102 30 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 182
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 182 (accept_3_2 28 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 65 182 13 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 65 182 (accept_3_2 25 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 65 182 (Polychromatic418967fa.accept_20_4_5_2_1_3119 24 65 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 182 (accept_3_2 22 65 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 182 (accept_3_2 19 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 182 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 182 (accept_3_2 16 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 182
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 65 182 13 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 65 182 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 65 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 182 (accept_3_2 10 65 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 182 (accept_3_2 7 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  182 (Polychromatic418967fa.accept_21_6_2_14_1_5688 6 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 65 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 182 (accept_3_2 4 65 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 182
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 182 (accept_3_2 1 65 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 182 (allA_of_3_0 64 64 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 182 (allA_succ_of_accept 62 63 182
  (Polychromatic418967fa.accept_19_5_6_11_1_6069 62 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 182 (accept_3_2 61 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 182 (accept_3_2 58 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 182 7 8 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 182 (accept_3_2 55 63 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 182 (accept_3_2 52 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 182 (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 182 7 7 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 182
  (Polychromatic418967fa.accept_25_23_13_7_1_10471 48 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 182 (accept_3_2 46 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 182
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 182 (accept_3_2 43 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63
  182 7 6 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 182 (accept_3_2 40 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 182 (Polychromatic418967fa.accept_16_7_15_6_1_1428 39 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 182 (Polychromatic418967fa.accept_20_18_3_2_1_5929 38 63
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 182 (accept_3_2 37 63 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 182 (Polychromatic418967fa.accept_11_3_8_6_1_788
  36 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 182 7 5 9 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 182 (accept_3_2 34
  63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 182 (Polychromatic418967fa.accept_19_13_6_11_1_7600 32 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 182 (accept_3_2 31 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 182 7 4 9 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 182
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 182 (Polychromatic418967fa.accept_28_26_7_14_1_10470 26 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 182 (accept_3_2 25 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23
  63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 182 (accept_3_2 22 63
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 182 7 3 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 182
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 182 (accept_3_2 19 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 182 (accept_3_2 16 63 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 182 7 2 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 182 (accept_3_2 13 63 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 182 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 63
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 182 (accept_3_2 10 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 182 (Polychromatic418967fa.accept_22_8_19_6_1_2511 8 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 182 7 1 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 182 (accept_3_2 4 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  182 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 182 (Polychromatic418967fa.accept_22_2_19_6_1_5421 2 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 182 (accept_3_2 1 63 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 182
  (allA_succ_of_accept 61 62 182 (accept_3_2 61 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62
  182 2 30 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  62 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 62 182 2 29 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 62 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 62 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 182 2 28 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 182 (accept_3_2 55 62 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 182 2 27 31 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 182
  (Polychromatic418967fa.accept_18_17_8_2_1_2622 53 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 182 2 26 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 62 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 182 2 25 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 182 (accept_3_2 49 62 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 182 2 24 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 182 (Polychromatic418967fa.accept_17_13_11_12_1_4131 47 62
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 182 2 23 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 182
  (Polychromatic418967fa.accept_11_1_7_6_1_378 45 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 182 2 22 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 62 182 (accept_3_2 43 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62
  182 2 21 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  62 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 62 182 2 20 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 62 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 62 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 182 2 19 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 182 (accept_3_2 37 62 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 182 2 18 31 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 182
  (Polychromatic418967fa.accept_18_17_8_2_1_2622 35 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 182 2 17 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 182 2 16 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 182 (accept_3_2 31 62 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 182 2 15 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 182 (Polychromatic418967fa.accept_19_10_5_11_1_7597 29 62
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 182 2 14 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 182
  (Polychromatic418967fa.accept_21_6_20_14_1_8837 27 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 182 2 13 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 182 (accept_3_2 25 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62
  182 2 12 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  62 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 182 2 11 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 62 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 182 2 10 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 182 (accept_3_2 19 62 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 182 2 9 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 182 (Polychromatic418967fa.accept_18_17_8_2_1_2622
  17 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 182 2 8 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 182 2 7 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 182 (accept_3_2 13 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  182 2 6 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 182 (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 182 2 5 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 182 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 62 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 182 2 4 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 182 (accept_3_2 7 62 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 182 2 3 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 182 2 2 31 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 182 2 1 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 182 (accept_3_2 1 62 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 182 (allA_of_3_0 61 61 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 182 (allA_succ_of_accept 59 60 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 182 2 29 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 182 2 28 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 182 (accept_3_2 55 60 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 182 2 27 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 182 2 26 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 182
  (Polychromatic418967fa.accept_19_13_3_11_1_4706 51 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 182 2 25 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 182 (accept_3_2 49 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  182 2 24 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 182 (Polychromatic418967fa.accept_19_9_3_11_1_7505 47 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 182 2 23 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 60 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 182 2 22 30 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 182 (accept_3_2 43 60 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 182 2 21 30 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 182 2 20 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 182 2 19 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 182 (accept_3_2 37 60 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 182 2 18 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 182 2 17 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 182
  (Polychromatic418967fa.accept_19_14_3_11_1_10469 33 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 60 182 2 16 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 60 182 (accept_3_2 31 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 182 2 15 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 182 (Polychromatic418967fa.accept_19_10_3_11_1_7587 29 60 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 182 2 14 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 182 (Polychromatic418967fa.accept_18_9_6_2_1_2619
  27 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 182 2 13 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 182 (accept_3_2 25
  60 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 182 2 12 30 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 182 2 11 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 182 2 10 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 182 (accept_3_2 19 60 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 182 2 9 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 60 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 182 2 8 30 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 182
  (Polychromatic418967fa.accept_21_15_18_14_1_5632 15 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 182 2 7 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 182 (accept_3_2 13 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 182 2 6 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 182 (Polychromatic418967fa.accept_21_11_18_14_1_5646 11 60 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 182 2 5 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 182 (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 60 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 182 2 4 30 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 182 (accept_3_2 7 60 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 182 2 3 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 182 2 2 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 182 2 1 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 182 (accept_3_2 1 60 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 182 (allA_succ_of_accept 58 59 182
  (accept_3_2 58 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 182 (accept_3_2 55 59 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 182 (Polychromatic418967fa.accept_17_3_8_12_1_6573 54 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 182 (accept_3_2 52 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 50 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 182 (accept_3_2 49 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 182
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 182 (accept_3_2 46 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 182 (accept_3_2 43 59 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 182 (accept_3_2 40 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 182 (Polychromatic418967fa.accept_17_4_8_12_1_9165 38 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 182 (accept_3_2 37 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 182 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 59
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 182 (accept_3_2 34 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 182 (accept_3_2 31 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 182 (accept_3_2 28 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 182 (accept_3_2 25 59 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 182
  (Polychromatic418967fa.accept_19_4_2_11_1_3409 23 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 182 (accept_3_2 22 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 182 (accept_3_2 19 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 59
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 182 (accept_3_2 16 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 182 (Polychromatic418967fa.accept_22_14_15_6_1_10468 14 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 182 (accept_3_2 13 59 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 182
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 182 (accept_3_2 10 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 182 (accept_3_2 7 59 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 182 (accept_3_2 4 59 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 182
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 182 (accept_3_2 1 59 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 182 (allA_of_3_0 58 58 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 182 (allA_succ_of_accept 56 57 182
  (Polychromatic418967fa.accept_23_10_11_21_1_10467 56 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 57 182 (accept_3_2 55 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 57 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 182 (accept_3_2 52 57 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 182 (accept_3_2 49 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 182 (accept_3_2 46 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 182 (accept_3_2 43 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 182 (accept_3_2 40 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 182
  (Polychromatic418967fa.accept_20_18_17_2_1_5941 38 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 182 (accept_3_2 37 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 182 (accept_3_2 34 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 182 (accept_3_2 31 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 182 (accept_3_2 28 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 182 (accept_3_2 25 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 182 (accept_3_2 22 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 182 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 182
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 182 (accept_3_2 19 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 182 (accept_3_2 16 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 182 (accept_3_2 13 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 182 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 182 (accept_3_2 10 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 182 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 182 (accept_3_2 7 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 182 (accept_3_2 4 57 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2
  57 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 182 (accept_3_2 1 57 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 182)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 182 (allA_succ_of_accept 55 56 182 (accept_3_2 55 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 182 2 27 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 56 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 182 2 26 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 51
  56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 182 2 25 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 56 182 7 7 8 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 56 182 2 24 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 182 2 23 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 182 (Polychromatic418967fa.accept_19_7_18_11_1_464 45 56 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 182 2 22 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 182 (accept_3_2 43 56 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 182 14 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 182 2 20 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 182
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 39 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 182 2 19 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 182 (accept_3_2 37 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  182 2 18 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56
  182 7 5 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56
  182 2 17 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  56 182 (Polychromatic418967fa.accept_24_9_8_14_1_10466 33 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 56 182 2 16 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 56 182 (accept_3_2 31 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 182 2 15 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 56 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 56 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 182 14 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 56 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 182 2 13 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 182 (accept_3_2 25
  56 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 182 2 12 28 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 182 2 11 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 56 182 7 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 56 182 2 10 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 182 (accept_3_2 19 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  182 2 9 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 182 2 8 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 182 (Polychromatic418967fa.accept_22_15_12_6_1_8744 15 56 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 182 14 1 4 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 182 (accept_3_2 13 56 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 182 2 6 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 182 2 5 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 182
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 56 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 182 2 4 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 56 182 7 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 56 182 2 3 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 56 182 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 56 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 182 2 2 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 182 (Polychromatic418967fa.accept_19_3_18_11_1_6074 3 56 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 182 2 1 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 182 (accept_3_2 1 56 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 182))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 182 (allA_of_3_0 55 55 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 182
  (allA_succ_of_accept 53 54 182 (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 54 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 182 2 26 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 51
  54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 182 2 25 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 182 (accept_3_2 49
  54 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 182 2 24 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 182 2 23 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 54 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 54 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 182 2 22 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 182 (accept_3_2 43 54 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 182 2 21 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 182 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 54 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 182 2 20 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 182 2 19 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 182 (accept_3_2 37 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54
  182 2 18 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  54 182 (Polychromatic418967fa.accept_25_10_4_7_1_10465 35 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 54 182 2 17 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 54 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 182 2 16 27 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 182 (accept_3_2 31 54 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 182 2 15 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 182
  (Polychromatic418967fa.accept_21_8_12_14_1_10464 29 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 54 182 2 14 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 54 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 182 2 13 27 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 182 (accept_3_2 25 54 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 182 2 12 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 182 2 11 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 54 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 182 2 10 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 182 (accept_3_2 19 54 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 182 2 9 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 54 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 182 2 8 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 182 2 7 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 182 (accept_3_2 13 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  182 2 6 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 182 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 182 2 5 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 54 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 182 2 4 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 182 (accept_3_2 7 54 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 182 2 3 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 54 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 182 2 2 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 182 2 1 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 182 (accept_3_2 1 54 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  182)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 182 (allA_succ_of_accept 52 53 182 (accept_3_2
  52 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 182 (accept_3_2 49 53 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 182 (accept_3_2 46 53
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 182 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 182 (accept_3_2 43 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 182 (accept_3_2 40 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 182
  (Polychromatic418967fa.accept_17_4_2_12_1_6554 38 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 182 (accept_3_2 37 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 182 (accept_3_2 34 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 182 (accept_3_2 31 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 182 (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 182 (accept_3_2 28 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 182
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 26 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 182 (accept_3_2 25 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 182 (accept_3_2 22 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 182 (accept_3_2 19 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 182 (Polychromatic418967fa.accept_20_18_13_2_1_10463 18 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 182 (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 182 (accept_3_2 16 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 182 (accept_3_2 13 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 182 (accept_3_2 10 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 182 (accept_3_2 7 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 182 (accept_3_2 4 53 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 182 (Polychromatic418967fa.accept_19_2_15_11_1_7497
  2 53 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 182 (accept_3_2 1 53
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 182)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 182 (allA_of_3_0 52 52 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 182
  (allA_succ_of_accept 50 51 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 51 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 182 (accept_3_2 49 51 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 182 (accept_3_2 46 51
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 182 (accept_3_2 43 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 182 (accept_3_2 40 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 182 (accept_3_2 37 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 182 (accept_3_2 34 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 182 (accept_3_2 31 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 182 (accept_3_2 28 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 182 (accept_3_2 25 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 182 (Polychromatic418967fa.accept_19_5_13_11_1_6089 24 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 182 (accept_3_2 22 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 182
  (Polychromatic418967fa.accept_16_4_3_6_1_6805 20 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 182 (accept_3_2 19 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 182 (accept_3_2 16 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 182 (Polychromatic418967fa.accept_21_15_9_14_1_10462 15 51 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 182 (accept_3_2 13 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 182 (accept_3_2 10 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 182 (accept_3_2 7 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  182 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 182 (accept_3_2 4 51 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 2
  51 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 182 (accept_3_2 1 51 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 182)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 182 (allA_succ_of_accept 49 50 182 (accept_3_2 49 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 182 2 24 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 182 (Polychromatic418967fa.accept_17_13_16_12_1_6562 47 50 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 182 2 23 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 182
  (Polychromatic418967fa.accept_17_11_16_12_1_1984 45 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 50 182 2 22 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 50 182 (accept_3_2 43 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 182 2 21 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 50 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 50 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 182 2 20 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 39
  50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 182 2 19 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 182 (accept_3_2 37
  50 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 182 2 18 25 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 50 182 2 17 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 50 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 50 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 182 2 16 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 182 (accept_3_2 31 50 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 182 2 15 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 182 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 50 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 182 2 14 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 182
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 182 2 13 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 50 182 (accept_3_2 25 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50
  182 2 12 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  50 182 (Polychromatic418967fa.accept_19_4_12_11_1_10461 23 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 50 182 2 11 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 50 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 182 2 10 25 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 182 (accept_3_2 19 50 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 182 2 9 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 182 2 8 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 182 2 7 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 182 (accept_3_2 13 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  182 2 6 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 182 2 5 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 182 (Polychromatic418967fa.accept_16_9_2_6_1_4434 9 50 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 182 2 4 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 182 (accept_3_2 7 50 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 182 2 3 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 182 (Polychromatic418967fa.accept_19_5_12_11_1_10460 5 50 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 182 2 2 25 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 182 2 1 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 182 (accept_3_2 1 50 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  182)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 182 (allA_of_3_0 49 49 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 182 (allA_succ_of_accept 47 48 182 (Polychromatic418967fa.accept_25_22_23_7_1_10459
  47 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 182 2 23 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 182 2 22 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 182 (accept_3_2 43 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  182 2 21 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 182 2 20 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 182 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 48 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 182 2 19 24 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 182 (accept_3_2 37 48 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 182 2 18 24 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 182
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 182 2 17 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 182 2 16 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 182 (accept_3_2 31 48 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 182 2 15 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 182 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 48 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 182 2 14 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 182
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 182 2 13 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 182 (accept_3_2 25 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  182 2 12 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 182 2 11 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 182 (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 48 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 182 2 10 24 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 182 (accept_3_2 19 48 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 182 2 9 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 182 2 8 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 182 2 7 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 182 (accept_3_2 13 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  182 2 6 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 182 (Polychromatic418967fa.accept_17_11_14_12_1_2995 11 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 182 2 5 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 182 (Polychromatic418967fa.accept_17_9_14_12_1_9177 9 48 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 182 2 4 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 182 (accept_3_2 7 48 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 182 2 3 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 182 2 2 24 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 182
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 182 2 1 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 182 (accept_3_2 1 48 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  182)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 182 (allA_succ_of_accept 46 47 182 (accept_3_2 46 47
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 182 (accept_3_2 43 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 182 (accept_3_2 40 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 182
  (Polychromatic418967fa.accept_20_18_7_2_1_4449 38 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 182 (accept_3_2 37 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 182 (Polychromatic418967fa.accept_19_17_9_11_1_6057 36 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 182 (accept_3_2 34 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 182 (accept_3_2 31 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 182 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 182 (accept_3_2 28 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 182
  (Polychromatic418967fa.accept_19_7_9_11_1_7493 26 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 182 (accept_3_2 25 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 182 (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 182 (accept_3_2 22 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 182
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 182 (accept_3_2 19 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 182 (Polychromatic418967fa.accept_17_1_13_12_1_1084 18 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 182 (accept_3_2 16 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 182 (accept_3_2 13 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 182 (Polychromatic418967fa.accept_20_12_7_2_1_4448 12 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 182 (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 182 (accept_3_2 10 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 182
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 182 (accept_3_2 7 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  182 (Polychromatic418967fa.accept_25_6_22_7_1_10458 6 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 182 (accept_3_2 4 47 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 182
  (Polychromatic418967fa.accept_19_2_9_11_1_7515 2 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 182 (accept_3_2 1 47 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  182))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 182 (allA_of_3_0 46 46 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 182 (allA_succ_of_accept 44 45 182 (Polychromatic418967fa.accept_20_4_5_2_1_3119 44
  45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 182 (accept_3_2 43 45
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 182
  (Polychromatic418967fa.accept_12_6_9_2_1_311 42 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 182 (accept_3_2 40 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 182 (Polychromatic418967fa.accept_10_8_5_2_1_881
  38 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 182 (accept_3_2 37
  45 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 182
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 182 (accept_3_2 34 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 182
  (Polychromatic418967fa.accept_19_13_7_11_1_7551 32 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 182 (accept_3_2 31 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 182 (accept_3_2 28 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 182
  (Polychromatic418967fa.accept_28_26_17_14_1_10457 26 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 182 (accept_3_2 25 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 182 (accept_3_2 22 45 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 182 (Polychromatic418967fa.accept_18_3_9_2_1_5053
  21 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 182
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 182 (accept_3_2 19 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 182 (accept_3_2 16 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 182
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 182 (accept_3_2 13 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 182 (Polychromatic418967fa.accept_19_12_7_11_1_7658 12 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 182 (accept_3_2 10 45 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 182 (Polychromatic418967fa.accept_16_9_13_6_1_2334
  9 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 182 (accept_3_2 7 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 182 (accept_3_2 4 45 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 182 (Polychromatic418967fa.accept_21_2_3_14_1_5690
  2 45 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 182 (accept_3_2 1 45
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 182))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  44 182 (allA_succ_of_accept 43 44 182 (accept_3_2 43 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  42 44 182 2 21 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 182 2 20 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 39
  44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 182 2 19 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 182 (accept_3_2 37
  44 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 182 2 18 22 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 182 2 17 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 182 2 16 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 182 (accept_3_2 31 44 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 182 2 15 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 44 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 182 2 14 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 182 2 13 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 182 (accept_3_2 25 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44
  182 2 12 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  44 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 182 2 11 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 182 2 10 22 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 182 (accept_3_2 19 44 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 182 2 9 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 182 (Polychromatic418967fa.accept_10_7_4_2_1_903 17
  44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 182 2 8 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 182 2 7 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 182 (accept_3_2 13 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  182 2 6 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 182 2 5 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 182 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 44 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 182 2 4 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 182 (accept_3_2 7 44 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 182 2 3 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 182 2 2 22 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 182 2 1 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 182 (accept_3_2 1 44 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  182)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 182 (allA_of_3_0 43 43 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 182 (allA_succ_of_accept 41 42 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 182 2 20 21 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 182 2 19 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 182 (accept_3_2 37 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  182 2 18 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42
  182 7 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42
  182 2 17 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  42 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 42 182 2 16 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 42 182 (accept_3_2 31 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 182 2 15 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 182 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 42 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 182 14 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 182 2 13 21 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 182 (accept_3_2 25
  42 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 182 2 12 21 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 182 2 11 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 182 7 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 42 182 2 10 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 182 (accept_3_2 19 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  182 2 9 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 182 2 8 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 42 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 182 14 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 182 (accept_3_2 13 42 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 182 2 6 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 182 (Polychromatic418967fa.accept_22_11_20_6_1_10456 11 42 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 182 2 5 21 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 182 2 4 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 42 182 7 1 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 42 182 2 3 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 182 2 2 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 182 2 1 21 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 182 (accept_3_2 1 42 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 182)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 182
  (allA_succ_of_accept 40 41 182 (accept_3_2 40 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 182 (Polychromatic418967fa.accept_17_4_7_12_1_6556 38 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 182 (accept_3_2 37 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 182 (accept_3_2 34 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 182 (accept_3_2 31 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 182
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 182 (accept_3_2 28 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 182 (accept_3_2 25 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 182 (accept_3_2 22 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 182 (accept_3_2 19 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 182 (accept_3_2 16 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 182 (accept_3_2 13 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 182 (accept_3_2 10 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 182 (accept_3_2 7 41 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 182
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 182 (accept_3_2 4 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 41 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 182 (accept_3_2 1 41 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 182))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 182 (allA_of_3_0 40 40 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 182 (allA_succ_of_accept 38 39 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 182 (accept_3_2 37 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 182 (Polychromatic418967fa.accept_21_15_18_14_1_5632 36 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 182 (accept_3_2 34 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 182 (accept_3_2 31 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 182 (accept_3_2 28 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 182 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 39 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 182 13 2 3 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 182 (accept_3_2 25 39 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 182 (accept_3_2 22 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 182 (Polychromatic418967fa.accept_21_20_18_14_1_10455 20 39 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 182 (accept_3_2 19 39 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 182 (accept_3_2 16 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 182 13 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 182 (Polychromatic418967fa.accept_18_12_3_2_1_756
  12 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 182 (accept_3_2 10 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 182 (accept_3_2 7 39 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 39 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 182 (accept_3_2 4 39 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 182 (Polychromatic418967fa.accept_19_3_1_11_1_10454
  3 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 182
  (Polychromatic418967fa.accept_22_2_17_6_1_10453 2 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 182 (accept_3_2 1 39 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  182))))))))))))))))))))))))))))))))))))))) (allB_succ 38 182 (allA_succ_of_accept 37 38 182 (accept_3_2 37 38 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 182 2 18 19 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 182 2 17 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 182 (Polychromatic418967fa.accept_20_13_18_2_1_10452 33 38 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 182 2 16 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 182 (accept_3_2 31 38 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 182 2 15 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 182 (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 38
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 182 2 14 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 182
  (Polychromatic418967fa.accept_20_7_18_2_1_10451 27 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 38 182 2 13 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 38 182 (accept_3_2 25 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38
  182 2 12 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  38 182 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 38 182 2 11 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 38 182 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 38 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 182 2 10 19 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 182 (accept_3_2 19 38 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 182 2 9 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 182 (Polychromatic418967fa.accept_20_17_18_2_1_8937
  17 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 182 2 8 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 38 182 2 7 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 38 182 (accept_3_2 13 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38
  182 2 6 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  38 182 (Polychromatic418967fa.accept_22_11_16_6_1_10450 11 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 182 2 5 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 38 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 38 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 182 2 4 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 182 (accept_3_2 7 38 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 182 2 3 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 38 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 38 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 182 2 2 19 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 182
  (Polychromatic418967fa.accept_20_3_18_2_1_5918 3 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 182 2 1 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 182 (accept_3_2 1 38 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  182)))))))))))))))))))))))))))))))))))))) (allB_succ 37 182 (allA_of_3_0 37 37 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 182 (allA_succ_of_accept 35 36 182 (Polychromatic418967fa.accept_16_3_4_6_1_6798 35 36 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 182 2 17 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 182
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 33 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 182 2 16 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 182 (accept_3_2 31 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 182 2 15 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 182 (Polychromatic418967fa.accept_16_13_4_6_1_2322 29 36 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 182 2 14 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760
  27 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 182 2 13 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 182 (accept_3_2 25
  36 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 182 2 12 18 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 182
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 182 2 11 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 36 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 182 2 10 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 182 (accept_3_2 19 36 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 182 2 9 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 36 182 (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 36 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 182 2 8 18 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 182
  (Polychromatic418967fa.accept_22_15_14_6_1_10449 15 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 182 2 7 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 182 (accept_3_2 13 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 182 2 6 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 182 2 5 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 36 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 182 2 4 18 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 182 (accept_3_2 7 36 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 182 2 3 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 182 (Polychromatic418967fa.accept_16_5_4_6_1_3349 5
  36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 182 2 2 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 182
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 182 2 1 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 182 (accept_3_2 1 36 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  182)))))))))))))))))))))))))))))))))))) (allB_succ 35 182 (allA_succ_of_accept 34 35 182 (accept_3_2 34 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 182 (accept_3_2 31 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 182 7 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 182
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 182 (accept_3_2 25 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 182 (accept_3_2 22 35 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35 182 7 3 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 35 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 182 (accept_3_2 19 35 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 182 (accept_3_2 16 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 35 182 7 2 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 35 182 (accept_3_2 13 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 35 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 182 (accept_3_2 10 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 35 182 7 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 35 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 182 (accept_3_2 4 35 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 182
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 182 (accept_3_2 1 35 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  182))))))))))))))))))))))))))))))))))) (allB_succ 34 182 (allA_of_3_0 34 34 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 182 (allA_succ_of_accept 32 33 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 33 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 182 (accept_3_2 31 33 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 30
  33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 182 (accept_3_2 28 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 182 (accept_3_2 25 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 182 (Polychromatic418967fa.accept_19_5_14_11_1_6084 24 33 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 182 (accept_3_2 22 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 182 (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 182 (accept_3_2 19 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 33 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 182 (accept_3_2 16 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 182 (accept_3_2 13 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 182 (accept_3_2 10 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 182 (Polychromatic418967fa.accept_19_9_14_11_1_7496 9 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 182 (accept_3_2 7 33 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 182 (accept_3_2 4 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 33 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 182 (accept_3_2 1 33 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 182))))))))))))))))))))))))))))))))) (allB_succ 32 182 (allA_succ_of_accept 31 32 182
  (accept_3_2 31 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 182 2 15 16 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 182 2 14 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 32 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 182 2 13 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 182 (accept_3_2 25 32 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 182 2 12 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 182 2 11 16 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 182 2 10 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 182 (accept_3_2 19 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  182 2 9 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 182 2 8 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 182 2 7 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 182 (accept_3_2 13 32 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 182 2 6 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 32 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 182 2 5 16 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 182
  (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 182 2 4 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 182 (accept_3_2 7 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 182
  2 3 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  182 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 32 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 182 2 2 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 32 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 182 2 1 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 182 (accept_3_2 1 32 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 182)))))))))))))))))))))))))))))))) (allB_succ 31 182 (allA_of_3_0 31 31 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 182 (allA_succ_of_accept 29 30 182
  (Polychromatic418967fa.accept_24_5_6_14_1_10448 29 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 182 2 14 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 182 2 13 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 182 (accept_3_2 25 30 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 182 2 12 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 182 2 11 15 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 182 2 10 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 182 (accept_3_2 19 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  182 2 9 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 182 2 8 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 182 2 7 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 182 (accept_3_2 13 30 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 182 2 6 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 182 (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 30 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 182 2 5 15 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 182 2 4 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 182 (accept_3_2 7 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 182
  2 3 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 182 2 2 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 30 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 30 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 182 2 1 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 182 (accept_3_2 1 30 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 182)))))))))))))))))))))))))))))) (allB_succ 29 182 (allA_succ_of_accept 28 29 182
  (accept_3_2 28 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 182 (Polychromatic418967fa.accept_21_5_8_14_1_5696 26 29 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 182 (accept_3_2 25 29 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 182 (Polychromatic418967fa.accept_19_5_10_11_1_10447 24 29 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 182 (accept_3_2 22 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 182 (accept_3_2 19 29 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 29 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 182
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 182 (accept_3_2 16 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 182 (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 29 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 182 (accept_3_2 13 29 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 182 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 29 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 182 (accept_3_2 10 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 29 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 182 (accept_3_2 7 29 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 182 (Polychromatic418967fa.accept_21_6_8_14_1_10446 6 29 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 182
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 182 (accept_3_2 4 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 182 (Polychromatic418967fa.accept_19_2_10_11_1_7616 2 29 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 182 (accept_3_2 1 29 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 182))))))))))))))))))))))))))))) (allB_succ 28 182 (allA_of_3_0 28 28 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 182 (allA_succ_of_accept 26 27 182 (Polychromatic418967fa.accept_19_7_8_11_1_3379
  26 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 182 (accept_3_2 25
  27 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 182
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 182 (accept_3_2 22 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820
  20 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 182 (accept_3_2 19
  27 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 182
  (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 182 (accept_3_2 16 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 182 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 27 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 182 (Polychromatic418967fa.accept_10_4_7_2_1_211
  14 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 182 (accept_3_2 13
  27 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 182
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 182 (accept_3_2 10 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 182 (Polychromatic418967fa.accept_17_8_10_12_1_5335
  8 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 182 (accept_3_2 7 27
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 182
  (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 182 (accept_3_2 4 27 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 27 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 182 (Polychromatic418967fa.accept_16_2_11_6_1_737 2
  27 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 182 (accept_3_2 1 27 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 182))))))))))))))))))))))))))) (allB_succ 26 182
  (allA_succ_of_accept 25 26 182 (accept_3_2 25 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  182 2 12 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 182 2 11 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 182 2 10 13 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 182 (accept_3_2 19 26 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 182 2 9 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 182 (Polychromatic418967fa.accept_18_17_8_2_1_2622
  17 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 182 2 8 13 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 182
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 182 2 7 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 26 182 13 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 26 182 2 6 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 26 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 26 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 182 2 5 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 182 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 26 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 182 2 4 13 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 182 (accept_3_2 7 26 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 182 2 3 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 182 2 2 13 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 182 2 1 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 182 (accept_3_2 1 26 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  182)))))))))))))))))))))))))) (allB_succ 25 182 (allA_of_3_0 25 25 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 182 (allA_succ_of_accept 23 24 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 182 2 11 12 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 182 2 10 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 182 (accept_3_2 19 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  182 2 9 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 182 2 8 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 182 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 24 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 182 2 7 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 182 (accept_3_2 13 24 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 182 2 6 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 182 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 24 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 182 2 5 12 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 182
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 182 2 4 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 182 (accept_3_2 7 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 182
  2 3 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 182 2 2 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 182 2 1 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 182 (accept_3_2 1 24 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 182)))))))))))))))))))))))) (allB_succ 23 182 (allA_succ_of_accept 22 23 182 (accept_3_2 22
  23 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 23 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 182 (accept_3_2 19 23 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 182 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 23 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 182 (accept_3_2 16 23
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 182 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 182
  (Polychromatic418967fa.accept_27_14_23_20_1_10445 14 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 23 182 (accept_3_2 13 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 23 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 23 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 182 (accept_3_2 10 23 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 182 (accept_3_2 7 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 182 (accept_3_2 4 23 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 182 (Polychromatic418967fa.accept_17_2_6_12_1_7912
  2 23 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 182 (accept_3_2 1 23
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 182))))))))))))))))))))))) (allB_succ 22 182 (allA_of_3_0 22
  22 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 182 (allA_succ_of_accept 20 21 182
  (Polychromatic418967fa.accept_16_4_5_6_1_8071 20 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 182 (accept_3_2 19 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 182 (accept_3_2 16 21 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 21 182 7 2 3 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 182 (accept_3_2 13 21 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 182 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 21
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 182 (accept_3_2 10 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 182 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 182 7 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 182 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 182 (accept_3_2 4 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 182 (Polychromatic418967fa.accept_17_2_4_12_1_6587 2 21 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 182 (accept_3_2 1 21 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 182))))))))))))))))))))) (allB_succ 20 182 (allA_succ_of_accept 19 20 182 (accept_3_2 19 20
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 182 2 9 10 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 20 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 182 2 8 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 182 (Polychromatic418967fa.accept_17_15_3_12_1_9179 15 20 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 182 2 7 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 182 (accept_3_2 13 20 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 182 2 6 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 182 2 5 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 182 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9
  20 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 182 2 4 10 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 182 (accept_3_2 7 20
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 182 2 3 10 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 20 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 182 2 2 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 20 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 182 2 1 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 182 (accept_3_2 1 20 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 182)))))))))))))))))))) (allB_succ 19 182 (allA_of_3_0 19 19 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 182 (allA_succ_of_accept 17 18 182 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 18 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 182 2 8 9 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 182
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 182 2 7 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 182 (accept_3_2 13 18 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  182 2 6 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 182 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 18 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 182 2 5 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 18 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 182 2 4 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 182 (accept_3_2 7 18 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 182 2 3 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 18 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 182 2 2 9 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 18 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 182 2 1 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 182 (accept_3_2 1 18 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  182)))))))))))))))))) (allB_succ 17 182 (allA_succ_of_accept 16 17 182 (accept_3_2 16 17 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 182 (accept_3_2 13 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 182 (accept_3_2 10 17 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 182
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 182 (accept_3_2 7 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 182 (accept_3_2 4 17 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2
  17 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 182 (accept_3_2 1 17 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 182))))))))))))))))) (allB_succ 16 182 (allA_of_3_0 16 16 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 182 (allA_succ_of_accept 14 15 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 182 (accept_3_2 13 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 182 (accept_3_2 10 15 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 182 (accept_3_2 7 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 182 (accept_3_2 4 15 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2
  15 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 182 (accept_3_2 1 15 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 182))))))))))))))) (allB_succ 14 182 (allA_succ_of_accept 13 14
  182 (accept_3_2 13 14 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 182 2 6 7 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 182
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 11 14 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 14 182 2 5 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 14 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 14 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 182 2 4 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 14 182 7 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 14 182 2 3 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 182 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5
  14 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 182 2 2 7 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 14 182 2 1 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 14 182 (accept_3_2 1 14 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  182)))))))))))))) (allB_succ 13 182 (allA_of_3_0 13 13 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 182
  (allA_succ_of_accept 11 12 182 (Polychromatic418967fa.accept_21_11_12_14_1_5670 11 12 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 182 2 5 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 182 (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 12 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 182 2 4 6 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 182 (accept_3_2 7 12 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 182 2 3 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 182 2 2 6 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 182
  (Polychromatic418967fa.accept_15_3_12_2_1_507 3 12 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 182 2 1 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 182 (accept_3_2 1 12 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12
  182)))))))))))) (allB_succ 11 182 (allA_succ_of_accept 10 11 182 (accept_3_2 10 11 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 11 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 182 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  8 11 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 182 (accept_3_2 7 11
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 182
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 182 (accept_3_2 4 11 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 182 (Polychromatic418967fa.accept_16_2_11_6_1_737 2
  11 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 182 (accept_3_2 1 11 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 182))))))))))) (allB_succ 10 182 (allA_of_3_0 10 10 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 182 (allA_succ_of_accept 8 9 182
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 9 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 182 (accept_3_2 7 9 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 182
  (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 182 (accept_3_2 4 9 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2
  9 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 182 (accept_3_2 1 9 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 182))))))))) (allB_succ 8 182 (allA_succ_of_accept 7 8 182
  (accept_3_2 7 8 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 182 2 3 4 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 182 2 2 4 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 8 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 182 2 1 4 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 182 (accept_3_2 1 8 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 182)))))))) (allB_succ 7 182 (allA_of_3_0 7 7 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 182 (allA_succ_of_accept 5 6 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 182 2 2 3 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 182 2 1 3 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 182 (accept_3_2 1 6
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 182)))))) (allB_succ 5 182 (allA_succ_of_accept 4 5 182
  (accept_3_2 4 5 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 182 (Polychromatic418967fa.accept_25_2_5_7_1_10444 2 5 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 182 (accept_3_2 1 5 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 182))))) (allB_succ 4 182 (allA_of_3_0 4 4 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 182 (allA_succ_of_accept 2 3 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 3 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 182 (accept_3_2 1 3 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 182))) (allB_succ 2 182 (allA_succ_of_accept 1 2 182 (accept_3_2 1 2 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 182)) (allB_two
  182))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


