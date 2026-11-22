-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch153
-- name    : Polychromatic418967fa_Branch153
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:04.482341+00:00
-- url     : https://prove2.me/theorems/8cfdc3b7-71ce-4fa7-b66b-f655a00cb960
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch153_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_153 : allB 153 153 :=
  allB_succ' 2 152 153 (Eq.refl Bool.true) (allA_succ_of_accept 1 152 153 (accept_3_4 1 152 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 153)) (allB_succ' 3 151 153 (Eq.refl Bool.true) (allA_succ_of_accept 2 151 153
  (accept_3_5 2 151 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 153
  (Polychromatic418967fa.accept_27_1_16_18_1_2547 1 151 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 151 153))) (allB_succ' 4 150 153 (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 153 3 1 50 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 153 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 150 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 150 153)))) (allB_succ' 5 149 153 (Eq.refl Bool.true) (allA_succ_of_accept 4
  149 153 (accept_3_4 4 149 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 153
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 149 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 149 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 153 (accept_3_4 1 149 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 149 153))))) (allB_succ' 6 148 153 (Eq.refl Bool.true) (allA_succ_of_accept 5 148 153
  (accept_3_5 5 148 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 153
  (Polychromatic418967fa.accept_11_4_5_10_1_926 4 148 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 148 153 (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 148 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 153 (accept_3_5 2 148 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 148 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 153)))))) (allB_succ' 7 147 153 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 147 153 3 2 49 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 153 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 147 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 153 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 147 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 153 3 1 49 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 147 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147 153))))))) (allB_succ' 8 146 153 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 153 (accept_3_4 7 146 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 153 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 146 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 146 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 153 (accept_3_4 4 146 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 153
  (Polychromatic418967fa.accept_13_2_3_10_1_658 2 146 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 153 (accept_3_4 1 146 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  153)))))))) (allB_succ' 9 145 153 (Eq.refl Bool.true) (allA_succ_of_accept 8 145 153 (accept_3_5 8 145 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 145 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 153
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 145 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 153 (accept_3_5 5 145 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 153 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 145 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 153 (accept_3_5 2 145 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 153))))))))) (allB_succ' 10 144 153 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 153 9 1 16 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 144 153 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 144 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 153 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  144 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 153 3 2 48 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 153 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 144 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 153 3 1 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 144 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 153
  (Polychromatic418967fa.accept_23_1_6_15_1_8340 1 144 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 153)))))))))) (allB_succ' 11 143 153 (Eq.refl Bool.true) (allA_succ_of_accept 10 143 153 (accept_3_4 10
  143 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 143 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 143 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 153 (accept_3_4 7 143 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 143 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 153 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  143 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 153 (accept_3_4 4 143
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 153
  (Polychromatic418967fa.accept_12_3_11_9_1_193 3 143 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 143 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 153 (accept_3_4 1 143 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 143 153))))))))))) (allB_succ' 12 142 153 (Eq.refl Bool.true) (allA_succ_of_accept 11 142 153
  (accept_3_5 11 142 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 153
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 142 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 142 153 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 142 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 153 (accept_3_5 8 142 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 142 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 153 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 142 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 153 (accept_3_5 5
  142 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 153
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 142 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 142 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 153 (accept_3_5 2 142 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 142 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 142 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 153)))))))))))) (allB_succ' 13 141 153 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 141 153 3 4 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 153 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 141 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 153 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 141
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 153 3 3 47 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 153
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 141 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 153 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 141 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 153 3 2 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 153
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 141 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 153 3 1 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 153 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 141 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 153))))))))))))) (allB_succ' 14 140 153
  (Eq.refl Bool.true) (allA_succ_of_accept 13 140 153 (accept_3_4 13 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 140 153 (Polychromatic418967fa.accept_19_12_7_1_1_5400 12 140 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 153 (accept_3_4 10 140 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 153 (Polychromatic418967fa.accept_11_9_8_10_1_934
  9 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 153
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 153 (accept_3_4 7 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 153 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 153 (accept_3_4 4 140 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 153 (Polychromatic418967fa.accept_16_3_12_9_1_8250 3 140 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 153
  (Polychromatic418967fa.accept_15_2_5_3_1_552 2 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 153 (accept_3_4 1 140 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  153)))))))))))))) (allB_succ' 15 139 153 (Eq.refl Bool.true) (allA_succ_of_accept 14 139 153 (accept_3_5 14 139 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 153
  (Polychromatic418967fa.accept_22_13_7_21_1_8339 13 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 153 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 139 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 153 (accept_3_5 11 139 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 153
  (Polychromatic418967fa.accept_20_9_19_13_1_8338 9 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 153 (accept_3_5 8 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 153 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 153 (accept_3_5 5 139 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 153
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 153 (accept_3_5 2 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 153 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 139 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 153))))))))))))))) (allB_succ' 16 138 153 (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 153 3
  5 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138
  153 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 138 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 138 153 (Polychromatic418967fa.accept_27_13_3_18_1_8337 13 138 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 153 3 4 46 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 153 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 138 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 153 3 3 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 138 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 153 3 2 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 153 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 138 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 138 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 153 3 1 46 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 153
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 138 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 138 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 153)))))))))))))))) (allB_succ' 17 137 153 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 137 153 (accept_3_4 16 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 153 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 137 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 153 (accept_3_4 13 137 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 153 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 153
  (Polychromatic418967fa.accept_23_11_22_15_1_8336 11 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 153 (accept_3_4 10 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 137 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 153 (accept_3_4 7 137 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 153 (Polychromatic418967fa.accept_10_6_7_3_1_547 6
  137 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 153 (accept_3_4 4 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 153 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 137 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 137 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 153 (accept_3_4 1 137 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 153))))))))))))))))) (allB_succ' 18 136 153 (Eq.refl Bool.true) (allA_succ_of_gcd
  17 136 153 17 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 16 136 153 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 136 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 153 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 136
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 153 (accept_3_5 14 136
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 153
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 136 153 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 136 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 153 (accept_3_5 11 136 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 136 153 (Polychromatic418967fa.accept_19_10_3_1_1_8312 10 136 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 153 (accept_3_5 8 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 153 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 136 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 153 (accept_3_5 5 136 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 153 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 136 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 153
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 153 (accept_3_5 2 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 153)))))))))))))))))) (allB_succ' 19 135 153 (Eq.refl Bool.true) (allA_succ_of_gcd 18 135
  153 9 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  135 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 153 (Polychromatic418967fa.accept_21_16_9_6_1_8335 16 135 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 153 3 5 45 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 135 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 153 3 4 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 153 9 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 153 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 153 3 2 45 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 153
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 153 3 1 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 153
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 135 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 153))))))))))))))))))) (allB_succ' 20 134 153 (Eq.refl Bool.true) (allA_succ_of_accept 19 134 153
  (accept_3_4 19 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 153
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 134 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 153 (accept_3_4 16 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 134 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 153 (Polychromatic418967fa.accept_13_1_4_10_1_622
  14 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 153 (accept_3_4 13
  134 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 153
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 134 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 153 (accept_3_4 10 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 134 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 153 (Polychromatic418967fa.accept_13_8_4_10_1_4358
  8 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 153 (accept_3_4 7
  134 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 153
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 134 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 153 (accept_3_4 4 134 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 134 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  134 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 153 (accept_3_4 1 134
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 153)))))))))))))))))))) (allB_succ' 21 133 153 (Eq.refl
  Bool.true) (allA_succ_of_accept 20 133 153 (accept_3_5 20 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 133 153 (Polychromatic418967fa.accept_13_6_3_10_1_698 19 133 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 153 (Polychromatic418967fa.accept_21_18_7_6_1_3609 18 133
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 153 (accept_3_5 17 133
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 153
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 133 153 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 133 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 153 (accept_3_5 14 133 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 133 153 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 133 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 153
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 153 (accept_3_5 11 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 153 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 133 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 153 (accept_3_5 8 133 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 153 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 133 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 153
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 153 (accept_3_5 5 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 153 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 133 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 153 (accept_3_5 2 133 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 153 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 133 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 153))))))))))))))))))))) (allB_succ' 22 132 153
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 153 3 7 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 132 153 (Polychromatic418967fa.accept_18_2_6_9_1_1032 20 132 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 153
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 153 3 6 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 153 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 132 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 153 (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 132
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 153 3 5 44 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 153
  (Polychromatic418967fa.accept_16_14_4_9_1_1646 14 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 153 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 153 3 4 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 153 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  11 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 153
  (Polychromatic418967fa.accept_20_10_12_13_1_8268 10 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 132 153 3 3 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 132 153 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 132 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 153 (Polychromatic418967fa.accept_14_7_6_13_1_4111
  7 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 153 3 2 44 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 153
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 153 (Polychromatic418967fa.accept_25_4_7_3_1_8334 4 132 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 153 3 1 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 153 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 132 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 153
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 132 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 153)))))))))))))))))))))) (allB_succ' 23 131 153 (Eq.refl Bool.true) (allA_succ_of_accept 22 131 153
  (accept_3_4 22 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 153
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 131 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 153 (accept_3_4 19 131 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 131 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 153 (Polychromatic418967fa.accept_13_4_1_10_1_693
  17 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 153 (accept_3_4 16
  131 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 153
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 131 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 153 (accept_3_4 13 131 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 131 153 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 131 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 153
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 153 (accept_3_4 10 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 153 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 153 (accept_3_4 7 131 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 153
  (Polychromatic418967fa.accept_25_5_6_3_1_8333 5 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 153 (accept_3_4 4 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 153 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 131 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 153 (accept_3_4 1 131 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 153))))))))))))))))))))))) (allB_succ' 24 130 153 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 130 153 (accept_3_5 23 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 153 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 153 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 130 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 153 (accept_3_5 20 130 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 153
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 153 (accept_3_5 17 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 130 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 153 (accept_3_5 14 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 130 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 153 (accept_3_5 11 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 153 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 153 (accept_3_5 8 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 153
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 153 (accept_3_5 5 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 153 (Polychromatic418967fa.accept_19_4_16_1_1_8332 4 130 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 153 (accept_3_5 2 130 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 130 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 153)))))))))))))))))))))))) (allB_succ' 25 129 153
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 129 153 3 8 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 129 153 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 129 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 153
  (Polychromatic418967fa.accept_13_9_12_10_1_242 22 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 153 3 7 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 153 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 129 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 153 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 129
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 153 3 6 43 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 153
  (Polychromatic418967fa.accept_19_17_15_1_1_8300 17 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 129 153 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 153 3 5 43 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 153
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 153 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 129 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 153 3 4 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 153 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 153
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 129 153 3 3 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 129 153 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 129 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 153
  (Polychromatic418967fa.accept_13_7_12_10_1_640 7 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 153 3 2 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 153 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 129 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 153 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 153 3 1 43 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 153 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 129 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 153))))))))))))))))))))))))) (allB_succ' 26 128 153 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 128 153 (accept_3_4 25 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 153 (accept_3_4 22 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 153 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 128 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 153
  (Polychromatic418967fa.accept_15_5_8_3_1_556 20 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 153 (accept_3_4 19 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 153 (accept_3_4 16 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 153 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 128 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 153
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 153 (accept_3_4 13 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 153 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 153 (accept_3_4 10 128 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 153 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 128 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 153
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 153 (accept_3_4 7 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 153 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 153 (accept_3_4 4 128 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 128 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 153
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 153 (accept_3_4 1 128 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  153)))))))))))))))))))))))))) (allB_succ' 27 127 153 (Eq.refl Bool.true) (allA_succ_of_accept 26 127 153 (accept_3_5
  26 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 153
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 127 153 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 127 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 153 (accept_3_5 23 127 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 127 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 153 (Polychromatic418967fa.accept_14_7_1_13_1_357
  21 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 153 (accept_3_5 20
  127 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 153
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 127 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 153 (accept_3_5 17 127 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 127 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 153 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 153 (accept_3_5 14
  127 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 153
  (Polychromatic418967fa.accept_22_13_17_21_1_8331 13 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 153 (accept_3_5 11 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 153
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 153 (accept_3_5 8 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 153 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 153 (accept_3_5 5 127 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 153
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 153 (accept_3_5 2 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 153 (Polychromatic418967fa.accept_22_1_17_21_1_8330 1 127 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 153))))))))))))))))))))))))))) (allB_succ' 28 126 153 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 126 153 9 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 153 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 153 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 126
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 153 3 8 42 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 153 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 153 3 7 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 153 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 153 9 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 153 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 153 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 126
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 153 3 5 42 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 126 153
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 153 (Polychromatic418967fa.accept_19_13_12_1_1_3993 13 126 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 153 3 4 42 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 153 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 153 9 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 153 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 153 3 2 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 153 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 153 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 126 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 153 3 1 42 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 153
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 126 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 153 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 126 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126 153)))))))))))))))))))))))))))) (allB_succ' 29 125 153 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 125 153 (accept_3_4 28 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 125 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 125 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 153 (accept_3_4 25 125 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 153
  (Polychromatic418967fa.accept_13_11_8_10_1_676 24 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 153 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 125 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 153 (accept_3_4 22 125 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 153 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 153 (accept_3_4 19 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 153 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 153 (accept_3_4 16 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 125
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 153 (accept_3_4 13 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 153 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 153 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 153 (accept_3_4 10 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 153 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 125 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 153 (accept_3_4 7 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 153 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 153 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 125 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 153 (accept_3_4 4 125 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 125 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 153 (accept_3_4 1 125 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  153))))))))))))))))))))))))))))) (allB_succ' 30 124 153 (Eq.refl Bool.true) (allA_succ_of_accept 29 124 153
  (accept_3_5 29 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 153
  (Polychromatic418967fa.accept_19_9_10_1_1_8329 28 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 124 153 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 124 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 153 (accept_3_5 26 124 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 124 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 153
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 153 (accept_3_5 23 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 153 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 153 (accept_3_5 20 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 153
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 153 (accept_3_5 17 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 153 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 153 (accept_3_5 14 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 153
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 124 153 (accept_3_5 11 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 124 153 (Polychromatic418967fa.accept_22_10_14_21_1_8328 10 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 153 (Polychromatic418967fa.accept_10_9_4_3_1_539 9
  124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 153 (accept_3_5 8 124
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 153 (Polychromatic418967fa.accept_6_1_4_3_1_14
  7 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 153
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 153 (accept_3_5 5 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 124 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 153 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 153 (accept_3_5 2 124 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 153)))))))))))))))))))))))))))))) (allB_succ' 31 123
  153 (Eq.refl Bool.true) (allA_succ_of_gcd 30 123 153 3 10 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 153 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 123 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 153
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 153 3 9 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 123
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 153 3 8 41 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 153
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 153 3 7 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 153 (Polychromatic418967fa.accept_16_4_11_9_1_1631
  20 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 123 153 3 6 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 123 153 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 123 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 153 3 5 41 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 153 3 4 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 153 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 123 153 3 3 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 123 153 (Polychromatic418967fa.accept_19_8_9_1_1_3990 8 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 153 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 123 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 153 3 2 41 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 153 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 123 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 153 3 1 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 153
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 123 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123 153))))))))))))))))))))))))))))))) (allB_succ' 32 122 153 (Eq.refl Bool.true) (allA_succ_of_accept 31
  122 153 (accept_3_4 31 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 122 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 122 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 153 (accept_3_4 28 122 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 122 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 153 (Polychromatic418967fa.accept_19_7_8_1_1_4028
  26 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 153 (accept_3_4 25
  122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 153
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 122 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 153 (accept_3_4 22 122 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 122 153 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 122 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 153
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 153 (accept_3_4 19 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 153 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 153 (accept_3_4 16 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 153
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 153 (accept_3_4 13 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 153 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 153 (accept_3_4 10 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 153 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 153
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 153 (accept_3_4 7 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 153 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 153 (accept_3_4 4 122 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 153 (accept_3_4 1 122 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  153)))))))))))))))))))))))))))))))) (allB_succ' 33 121 153 (Eq.refl Bool.true) (allA_succ_of_accept 32 121 153
  (accept_3_5 32 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 153
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 121 153 (Polychromatic418967fa.accept_20_10_1_13_1_3848 30 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 153 (accept_3_5 29 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 153
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 153 (accept_3_5 26 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 153 (accept_3_5 23 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 153
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 153 (accept_3_5 20 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 153 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 153 (accept_3_5 17 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 153
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 153 (accept_3_5 14 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 153 (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 153 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 153 (accept_3_5 11 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 121 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 153
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 9 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 153 (accept_3_5 8 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 153 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 153 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 153 (accept_3_5 5 121 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 153
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 153 (accept_3_5 2 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 153 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 153))))))))))))))))))))))))))))))))) (allB_succ' 34 120 153 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 120 153 3 11 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 120 153 (Polychromatic418967fa.accept_13_6_3_10_1_698 32 120 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 153
  (Polychromatic418967fa.accept_16_15_8_9_1_2563 31 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 153 3 10 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 153 (Polychromatic418967fa.accept_18_11_12_9_1_992 29 120 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 153
  (Polychromatic418967fa.accept_13_2_3_10_1_658 28 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 120 153 3 9 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 120 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 153 (Polychromatic418967fa.accept_21_4_15_6_1_8327 25 120
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 153 3 8 40 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 153
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 153 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 120 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 153 3 7 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 153 (Polychromatic418967fa.accept_13_7_3_10_1_656
  20 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 153
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 153 3 6 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 153 (Polychromatic418967fa.accept_16_1_8_9_1_3462 17 120 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 120 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 153 3 5 40 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 153
  (Polychromatic418967fa.accept_19_14_6_1_1_4022 14 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 153 (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 120 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 153 3 4 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 153
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 120 153 (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 120 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 153 3 3 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 153
  (Polychromatic418967fa.accept_21_8_15_6_1_8247 8 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 153 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 120 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 153 3 2 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 153
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 120 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 120 153 3 1 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 120 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 120 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 153 (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 120 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 153))))))))))))))))))))))))))))))))))
  (allB_succ' 35 119 153 (Eq.refl Bool.true) (allA_succ_of_gcd 34 119 153 17 2 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 119 153
  (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 153 (accept_3_4 31 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 153
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 153 (accept_3_4 28 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 153 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 153 (accept_3_4 25 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 153 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 153
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 153 (accept_3_4 22 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 153 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 153 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 153 (accept_3_4 19 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 119 153 17 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 119 153 (accept_3_4 16 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 153 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 119
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 153 (accept_3_4 13 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 153 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 153 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 153 (accept_3_4 10 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 153 (Polychromatic418967fa.accept_19_9_5_1_1_2766 9 119 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 153 (accept_3_4 7 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 153 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 153 (accept_3_4 4 119 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 153 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 119 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 153 (accept_3_4 1 119 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  153))))))))))))))))))))))))))))))))))) (allB_succ' 36 118 153 (Eq.refl Bool.true) (allA_succ_of_accept 35 118 153
  (accept_3_5 35 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 153
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 34 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 118 153 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 118 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 153 (accept_3_5 32 118 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 118 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 153 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 153 (accept_3_5 29
  118 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 153
  (Polychromatic418967fa.accept_20_8_18_13_1_8326 28 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 153 (accept_3_5 26 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 118 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 153
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 153 (accept_3_5 23 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 153 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 153 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 118 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 153 (accept_3_5 20 118 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 153
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 153 (accept_3_5 17 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 153 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 153 (accept_3_5 14 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 118 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 153
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 118 153 (accept_3_5 11 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 118 153 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 153 (Polychromatic418967fa.accept_11_9_8_10_1_934
  9 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 153 (accept_3_5 8
  118 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 118 153 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 118 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 153 (accept_3_5 5 118 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 118 153 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 118 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 153 (accept_3_5 2 118
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 153 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 118 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  153)))))))))))))))))))))))))))))))))))) (allB_succ' 37 117 153 (Eq.refl Bool.true) (allA_succ_of_gcd 36 117 153 9 4 13
  17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 153
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 153 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 153 3 11 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 153
  (Polychromatic418967fa.accept_21_10_12_6_1_5124 31 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 117 153 3 10 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 117 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 117 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 153
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 153 9 3 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 153 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 117 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 153 3 8 39 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 153
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 153 3 7 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 153 (Polychromatic418967fa.accept_8_4_5_1_1_299 20
  117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 153
  (Polychromatic418967fa.accept_21_19_12_6_1_6689 19 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 117 153 9 2 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 117 153 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 117 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 153
  (Polychromatic418967fa.accept_10_6_7_3_1_547 16 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 153 3 5 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 153 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 153 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 117
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 153 3 4 39 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 153
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 153 (Polychromatic418967fa.accept_19_10_3_1_1_8312 10 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 153 9 1 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 153
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 153 3 2 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 153 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 153 3 1 39 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 153
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 117 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 153))))))))))))))))))))))))))))))))))))) (allB_succ' 38 116 153 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 153 (accept_3_4 37 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 116 153 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 116 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 153 (accept_3_4 34 116 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 153 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 153
  (Polychromatic418967fa.accept_13_6_12_10_1_690 32 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 153 (accept_3_4 31 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 153 (accept_3_4 28 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 153 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 116 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 153
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 153 (accept_3_4 25 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 153 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 153 (accept_3_4 22 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 153 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 116 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 153
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 153 (accept_3_4 19 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 153 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 153 (accept_3_4 16 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 153 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 116 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 153
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 116 153 (accept_3_4 13 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 116 153 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 116 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 153 (accept_3_4 10 116 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 153 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 153
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 153 (accept_3_4 7 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 153 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 153 (accept_3_4 4 116 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 153 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 153
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 153 (accept_3_4 1 116 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  153)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 115 153 (Eq.refl Bool.true) (allA_succ_of_accept 38 115 153
  (accept_3_5 38 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 115 153 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 115 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 153 (accept_3_5 35 115 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 153
  (Polychromatic418967fa.accept_21_12_10_6_1_1191 33 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 115 153 (accept_3_5 32 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 115 153 (Polychromatic418967fa.accept_20_11_15_13_1_8224 31 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 153 (accept_3_5 29
  115 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 153
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 115 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 153 (accept_3_5 26 115 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 153 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 153
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 153 (accept_3_5 23 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 153 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 115
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 153 (accept_3_5 20 115
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 153
  (Polychromatic418967fa.accept_27_19_7_18_1_4284 19 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 153 (accept_3_5 17 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 153
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 153 (accept_3_5 14 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 153 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 153 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 115 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 153 (accept_3_5 11 115 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 153
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 153 (accept_3_5 8 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 153 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 153 (accept_3_5 5 115 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 153 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 153
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 153 (accept_3_5 2 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 153 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 115 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 153))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 114 153 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 114 153 3 13 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 114 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 114 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 153 (Polychromatic418967fa.accept_10_7_4_3_1_560
  37 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 153 3 12 38 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 153 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 153 3 11 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 153
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 153 3 10 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 153 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 153 (Polychromatic418967fa.accept_12_4_6_9_1_548
  28 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 153 3 9 38 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 153
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 153 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 153 3 8 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 153
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 114 153 3 7 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 114 153 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 153 3 6 38 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 153
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 153 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 153 3 5 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 153 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 153
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 153 3 4 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 153 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 114 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 153 3 3 38 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 153
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 153 3 2 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 153 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 114 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 153
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 114 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 114 153 3 1 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 114 153 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 114 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 153 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 153))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 113 153 (Eq.refl Bool.true) (allA_succ_of_accept 40 113 153 (accept_3_4 40 113 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 153 (accept_3_4 37 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 153 (Polychromatic418967fa.accept_19_17_18_1_1_3980 36 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 153 (Polychromatic418967fa.accept_14_7_1_13_1_357 35 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 153 (accept_3_4 34 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 113 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 153 (accept_3_4 31 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 153 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 153 (accept_3_4 28 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 113
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 153 (accept_3_4 25 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 153 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 113 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 153 (accept_3_4 22 113 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 153 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 153 (accept_3_4 19 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 153 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 153 (Polychromatic418967fa.accept_19_17_18_1_1_3980 17 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 153 (accept_3_4 16 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 113
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 153 (accept_3_4 13 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 153 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 153 (accept_3_4 10 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 153 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 153 (accept_3_4 7 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 153 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 153 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 153 (accept_3_4 4 113 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 153 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 113 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 153
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 153 (accept_3_4 1 113 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  153))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 112 153 (Eq.refl Bool.true) (allA_succ_of_accept 41 112
  153 (accept_3_5 41 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 153
  (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 112 153 (Polychromatic418967fa.accept_20_19_12_13_1_2602 39 112 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 153 (accept_3_5 38 112 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 153
  (Polychromatic418967fa.accept_22_14_2_21_1_6583 36 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 112 153 (accept_3_5 35 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 112 153 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 112 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 153 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 112
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 153 (accept_3_5 32 112
  153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 153
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 112 153 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 112 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 153 (accept_3_5 29 112 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 112 153 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 153
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 153 (accept_3_5 26 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 153 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 153 (accept_3_5 23 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 153 (Polychromatic418967fa.accept_19_3_17_1_1_781 22 112
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 153
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 153 (accept_3_5 20 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 153 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 153 (accept_3_5 17 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 153 (Polychromatic418967fa.accept_19_16_17_1_1_4011 16 112
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 153
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 153 (accept_3_5 14 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 153 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 153 (accept_3_5 11 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 153 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 112
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 153
  (Polychromatic418967fa.accept_19_9_17_1_1_8325 9 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 153 (accept_3_5 8 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 153 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 112 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 153 (accept_3_5 5 112 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 153 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 112 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 153
  (Polychromatic418967fa.accept_19_3_17_1_1_781 3 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 153 (accept_3_5 2 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 153 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 153)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 111 153 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 111 153 3 14 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 153 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 111 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 153
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 153 3 13 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 153 (Polychromatic418967fa.accept_12_1_3_9_1_174
  37 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 153 3 12 37 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 153
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 153 3 11 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 153 (Polychromatic418967fa.accept_10_2_1_3_1_233
  32 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 153
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 153 3 10 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 153 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 111 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 153 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  28 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 153 3 9 37 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 153 3 8 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 153 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 153
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 153 3 7 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 153 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 153 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 111
  153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 153 3 6 37 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 153
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 153 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 153 3 5 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 153
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 153 3 4 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 153 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 153 3 3 37 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 153
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 153 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 153 3 2 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 153 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 111 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 153
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 111 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 153 3 1 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 153 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 153 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 111 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  153))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 110 153 (Eq.refl Bool.true) (allA_succ_of_accept 43 110
  153 (accept_3_4 43 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 153
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 110 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 110 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 153 (accept_3_4 40 110 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 153
  (Polychromatic418967fa.accept_13_12_6_10_1_667 38 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 153 (accept_3_4 37 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 153 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 153 (accept_3_4 34 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 153 (Polychromatic418967fa.accept_19_14_15_1_1_6806 33 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 153
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 153 (accept_3_4 31 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 153 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 153 (accept_3_4 28 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 153
  (Polychromatic418967fa.accept_23_3_18_15_1_8324 26 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 110 153 (accept_3_4 25 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 110 153 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 110 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 153 (accept_3_4 22 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 153 (Polychromatic418967fa.accept_15_6_5_3_1_1988
  21 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 153
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 20 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 110 153 (accept_3_4 19 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 110 153 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 110 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 153 (accept_3_4 16 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 153
  (Polychromatic418967fa.accept_19_14_15_1_1_6806 14 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 110 153 (accept_3_4 13 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 153 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 110 153 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 153 (accept_3_4 10 110 153
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 153 (Polychromatic418967fa.accept_13_9_6_10_1_666
  9 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 153
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 153 (accept_3_4 7 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 153 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 153 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 153 (accept_3_4 4 110 153 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 153 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 153 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 153
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 153 (accept_3_4 1 110 153 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  153))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_153_segment_000)))))))))))))))))))))))))))))))))))))))))))


