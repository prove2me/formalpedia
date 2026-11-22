-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch189
-- name    : Polychromatic418967fa_Branch189
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:04.87485+00:00
-- url     : https://prove2.me/theorems/2f809d82-9597-4505-9780-88eaa1f015a5
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch189_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_189 : allB 189 189 :=
  allB_succ' 2 188 189 (Eq.refl Bool.true) (allA_succ_of_accept 1 188 189 (accept_3_4 1 188 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 189)) (allB_succ' 3 187 189 (Eq.refl Bool.true) (allA_succ_of_accept 2 187 189
  (accept_3_5 2 187 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 189
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 187 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 187 189))) (allB_succ' 4 186 189 (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 189 3 1 62 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 186 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 186 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 186 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 189)))) (allB_succ' 5 185 189 (Eq.refl Bool.true) (allA_succ_of_accept 4
  185 189 (accept_3_4 4 185 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 189
  (Polychromatic418967fa.accept_12_3_5_9_1_176 3 185 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 185 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 189 (accept_3_4 1 185 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185 189))))) (allB_succ' 6 184 189 (Eq.refl Bool.true) (allA_succ_of_accept 5 184 189
  (accept_3_5 5 184 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 189
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 184 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 184 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 184 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 189 (accept_3_5 2 184 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 184 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 189)))))) (allB_succ' 7 183 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 183 189 3 2 61 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 183 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 183 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 189 3 1 61 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 183 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 189))))))) (allB_succ' 8 182 189 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  182 189 7 1 26 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 182 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 182 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 182 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 189 (accept_3_4 4 182 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 189
  (Polychromatic418967fa.accept_28_2_14_21_1_10813 2 182 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 182 189 (accept_3_4 1 182 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  182 189)))))))) (allB_succ' 9 181 189 (Eq.refl Bool.true) (allA_succ_of_accept 8 181 189 (accept_3_5 8 181 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500
  7 181 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 181 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 189 (accept_3_5 5 181 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 181 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 189 (accept_3_5 2 181 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 181 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 189))))))))) (allB_succ' 10 180 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 180 189 9 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 180 189 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 180 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 189 (Polychromatic418967fa.accept_16_7_4_13_1_1057
  7 180 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 189 3 2 60 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 5 180 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 180 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 189 3 1 60 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 180 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 180 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 189)))))))))) (allB_succ' 11 179 189 (Eq.refl Bool.true) (allA_succ_of_accept 10 179 189 (accept_3_4 10
  179 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 189
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 179 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 179 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 189 (accept_3_4 7 179 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 179 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 189 (Polychromatic418967fa.accept_15_5_14_9_1_274
  5 179 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 189 (accept_3_4 4
  179 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 189
  (Polychromatic418967fa.accept_12_3_11_9_1_193 3 179 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 179 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 189 (accept_3_4 1 179 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 179 189))))))))))) (allB_succ' 12 178 189 (Eq.refl Bool.true) (allA_succ_of_accept 11 178 189
  (accept_3_5 11 178 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 189
  (Polychromatic418967fa.accept_17_10_8_2_1_8411 10 178 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 178 189 (Polychromatic418967fa.accept_24_9_10_21_1_5526 9 178 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 189 (accept_3_5 8 178 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 178 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 178 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 189 (accept_3_5 5
  178 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 178 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 178 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 189 (accept_3_5 2 178 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 178 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 178 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 189)))))))))))) (allB_succ' 13 177 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 177 189 3 4 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 189 (Polychromatic418967fa.accept_18_11_15_9_1_360 11 177 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 177
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 189 3 3 59 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 189
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 177 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 189 (Polychromatic418967fa.accept_19_7_6_18_1_8123 7 177 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 189 3 2 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 177 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 177 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 189 3 1 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 177 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 177 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 189))))))))))))) (allB_succ' 14 176 189
  (Eq.refl Bool.true) (allA_succ_of_accept 13 176 189 (accept_3_4 13 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 176 189 (Polychromatic418967fa.accept_17_12_6_2_1_2346 12 176 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 189 (accept_3_4 10 176 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 189 (Polychromatic418967fa.accept_19_9_5_18_1_3891
  9 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 189
  (Polychromatic418967fa.accept_23_8_15_5_1_10862 8 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 189 (accept_3_4 7 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 189 (accept_3_4 4 176 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 176 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 189 (accept_3_4 1 176 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  189)))))))))))))) (allB_succ' 15 175 189 (Eq.refl Bool.true) (allA_succ_of_gcd 14 175 189 7 2 25 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 189
  (Polychromatic418967fa.accept_23_13_14_5_1_10990 13 175 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 175 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 189 (accept_3_5 11 175 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 175 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 189 (accept_3_5 8 175 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175
  189 7 1 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  175 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 175 189 (accept_3_5 5 175 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 175 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 175 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 189 (accept_3_5 2 175 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  175 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 189))))))))))))))) (allB_succ' 16
  174 189 (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 189 3 5 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 174 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 174 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 13 174 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 189 3 4 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 174
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 189 3 3 58 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 174 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 189 3 2 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 174 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 174 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 174 189 3 1 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 174 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 174 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 189 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 174 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 189)))))))))))))))) (allB_succ' 17 173 189
  (Eq.refl Bool.true) (allA_succ_of_accept 16 173 189 (accept_3_4 16 173 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 173 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 173 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 173 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 189 (accept_3_4 13 173 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 173 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 173 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 173 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 189 (accept_3_4 10 173 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 173 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 173 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  173 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 189 (accept_3_4 7 173
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 173 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 173 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 173 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 189 (accept_3_4 4 173 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 173 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 173 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2
  173 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 189 (accept_3_4 1 173
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173 189))))))))))))))))) (allB_succ' 18 172 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 189 (accept_3_5 17 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 172 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 16 172 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 189 (Polychromatic418967fa.accept_16_15_12_13_1_1045 15
  172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 189 (accept_3_5 14
  172 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 172 189 (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 172 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 189 (accept_3_5 11 172 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 172 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 189 (accept_3_5 8 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 172 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 189 (accept_3_5 5 172 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 172 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 189
  (Polychromatic418967fa.accept_14_3_4_7_1_175 3 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 189 (accept_3_5 2 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 189)))))))))))))))))) (allB_succ' 19 171 189 (Eq.refl Bool.true) (allA_succ_of_gcd 18 171
  189 9 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  171 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 171 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 171 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 189 3 5 57 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 171 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 189 3 4 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 189 9 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 171 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 171 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 189 3 2 57 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 171 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 189 3 1 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 171 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 189))))))))))))))))))) (allB_succ' 20 170 189 (Eq.refl Bool.true) (allA_succ_of_accept 19 170 189
  (accept_3_4 19 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 189
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 170 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 170 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 189 (accept_3_4 16 170 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 170 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 189
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 189 (accept_3_4 13 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 189 (accept_3_4 10 170 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 189 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 170 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 189 (accept_3_4 7 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 170 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 189 (accept_3_4 4 170 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 189
  (Polychromatic418967fa.accept_22_2_16_13_1_10861 2 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 170 189 (accept_3_4 1 170 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  170 189)))))))))))))))))))) (allB_succ' 21 169 189 (Eq.refl Bool.true) (allA_succ_of_accept 20 169 189 (accept_3_5 20
  169 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 189
  (Polychromatic418967fa.accept_26_19_13_7_1_10920 19 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 189 (Polychromatic418967fa.accept_17_1_16_2_1_1404 18 169 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 189 (accept_3_5 17 169 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 189 (accept_3_5 14 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 169 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 189 (accept_3_5 11 169 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 169 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 189 (accept_3_5 8 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 189 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 169 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 189 (accept_3_5 5 169 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 189 (accept_3_5 2 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 169 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 189))))))))))))))))))))) (allB_succ' 22 168 189 (Eq.refl Bool.true) (allA_succ_of_gcd 21 168
  189 21 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  168 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 20 168 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 168 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 168 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 189 3 6 56 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 189
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 168 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 189 (Polychromatic418967fa.accept_22_16_14_13_1_10858 16 168 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 189 3 5 56 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 189 7 2 24 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 168 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 189 3 4 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 168 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 168
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 189 3 3 56 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 189
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 168 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 168 189 7 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 168 189 3 2 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 168 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 168 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 189 3 1 56 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 189
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 168 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 168 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 189)))))))))))))))))))))) (allB_succ' 23 167 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 167 189 (accept_3_4 22 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 189 (Polychromatic418967fa.accept_19_2_15_18_1_1556 21 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 189 (accept_3_4 19 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 189 (accept_3_4 16 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 189 (accept_3_4 13 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 167 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 189 (accept_3_4 10 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 189 (accept_3_4 7 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 5 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 189 (accept_3_4 4 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 167 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 189 (accept_3_4 1 167 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 189))))))))))))))))))))))) (allB_succ' 24 166 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 166 189 (accept_3_5 23 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 166 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 189 (accept_3_5 20 166 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 189 (accept_3_5 17 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 189 (accept_3_5 14 166 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 166 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 189
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 166 189 (accept_3_5 11 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 166 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 166 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 189 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 166 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 189 (accept_3_5 8 166 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 189 (accept_3_5 5 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 166 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 189 (accept_3_5 2 166 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 166 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 189)))))))))))))))))))))))) (allB_succ' 25 165 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 165 189 3 8 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 165 189 (Polychromatic418967fa.accept_17_6_12_2_1_10966 23 165 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 189
  (Polychromatic418967fa.accept_23_22_4_5_1_10884 22 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 165 189 3 7 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 165 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 165 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 189 3 6 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 165 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 165
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 189 3 5 55 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 189 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 165 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 189 3 4 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 189 (Polychromatic418967fa.accept_10_1_5_9_1_157
  11 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 189
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 165 189 3 3 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 165 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 165 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 189 (Polychromatic418967fa.accept_17_7_12_2_1_7105
  7 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 189 3 2 55 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 189
  (Polychromatic418967fa.accept_19_5_13_18_1_5249 5 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 165 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 189 3 1 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 165 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 165 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 189))))))))))))))))))))))))) (allB_succ' 26 164 189 (Eq.refl Bool.true) (allA_succ_of_accept 25 164 189
  (accept_3_4 25 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 189
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 164 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 189 (accept_3_4 22 164 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 164 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 164 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 20 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 189 (accept_3_4 19 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 189 (accept_3_4 16 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 164 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 189
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 189 (accept_3_4 13 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 189 (accept_3_4 10 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 164 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 189 (accept_3_4 7 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 189 (accept_3_4 4 164 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 164 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 189
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 189 (accept_3_4 1 164 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  189)))))))))))))))))))))))))) (allB_succ' 27 163 189 (Eq.refl Bool.true) (allA_succ_of_accept 26 163 189 (accept_3_5
  26 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 189
  (Polychromatic418967fa.accept_17_8_10_2_1_4546 25 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 163 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 163 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 189 (accept_3_5 23 163 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 163 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 189 (Polychromatic418967fa.accept_18_3_1_9_1_1929
  21 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 189 (accept_3_5 20
  163 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 19 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 163 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 189 (accept_3_5 17 163 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 163 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 189 (Polychromatic418967fa.accept_11_4_9_2_1_259
  15 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 189 (accept_3_5 14
  163 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 189
  (Polychromatic418967fa.accept_31_13_8_3_1_10989 13 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 163 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 189 (accept_3_5 11 163 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 189
  (Polychromatic418967fa.accept_29_9_18_15_1_10988 9 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 163 189 (accept_3_5 8 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 163 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 163 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 189 (accept_3_5 5 163 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4
  163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 189 (accept_3_5 2 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 189 (Polychromatic418967fa.accept_16_1_3_13_1_2785 1 163 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 189))))))))))))))))))))))))))) (allB_succ' 28 162 189 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 162 189 27 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 162 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 162
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 189 3 8 54 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 162 189 3 7 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 162 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 189 9 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 162
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 189 3 5 54 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 189 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 189 3 4 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 162 189 9 1 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 162 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 189 3 2 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 162 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 189 3 1 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 162 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 162 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 189)))))))))))))))))))))))))))) (allB_succ' 29 161 189 (Eq.refl Bool.true) (allA_succ_of_gcd 28 161 189
  7 4 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 161
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 161 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 189 (accept_3_4 25 161 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 161 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 189
  (Polychromatic418967fa.accept_31_23_6_3_1_10987 23 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 161 189 (accept_3_4 22 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 161 189 7 3 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 161 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 189 (accept_3_4 19 161 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 161 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 161 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 17 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 189 (accept_3_4 16 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 161 189 7 2 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 161 189 (accept_3_4 13 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 161 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 161 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 161
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 189 (accept_3_4 10 161
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 161 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 161 189 7 1 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 161 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6 161 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 189 (accept_3_4 4 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 161 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 161 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 189 (accept_3_4 1 161 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 189))))))))))))))))))))))))))))) (allB_succ' 30 160 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 160 189 (accept_3_5 29 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 189 (Polychromatic418967fa.accept_19_9_8_18_1_1571 28 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 189 (accept_3_5 26 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 189 (accept_3_5 23 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 189 (Polychromatic418967fa.accept_23_21_22_5_1_10986 21 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 189 (accept_3_5 20 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 189 (accept_3_5 17 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 189 (accept_3_5 14 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 189 (accept_3_5 11 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 189 (accept_3_5 8 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 189 (accept_3_5 5 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 160 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 189 (accept_3_5 2 160 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 189)))))))))))))))))))))))))))))) (allB_succ' 31 159
  189 (Eq.refl Bool.true) (allA_succ_of_gcd 30 159 189 3 10 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 159 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 189
  (Polychromatic418967fa.accept_16_12_15_13_1_3872 28 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 159 189 3 9 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 159 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 189 3 8 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 159 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 189 3 7 53 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 189
  (Polychromatic418967fa.accept_19_1_7_18_1_10869 20 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 159 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 159 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 189 3 6 53 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 159 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 189 3 5 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 189 3 4 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 159 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 189 3 3 53 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 159 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 189 3 2 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 159 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 159 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 189 3 1 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 159 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 189)))))))))))))))))))))))))))))))
  (allB_succ' 32 158 189 (Eq.refl Bool.true) (allA_succ_of_accept 31 158 189 (accept_3_4 31 158 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 189 (accept_3_4 28 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 189 (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 189 (accept_3_4 25 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 158
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 158 189 (accept_3_4 22 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 158 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 189 (accept_3_4 19 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 158
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 189 (accept_3_4 16 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 189 (accept_3_4 13 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 189 (Polychromatic418967fa.accept_19_12_6_18_1_8095 12 158
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 189 (accept_3_4 10 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 158 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 189 (accept_3_4 7 158 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 158 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 189 (accept_3_4 4 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2 158 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 189 (accept_3_4 1 158 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 189)))))))))))))))))))))))))))))))) (allB_succ' 33 157 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 157 189 (accept_3_5 32 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 31 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 189 (Polychromatic418967fa.accept_20_10_17_9_1_3491 30 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 189 (accept_3_5 29 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 189 (accept_3_5 26 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 189 (accept_3_5 23 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 157 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 189 (accept_3_5 20 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 189 (accept_3_5 17 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 189 (accept_3_5 14 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 189 (accept_3_5 11 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 157 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 189
  (Polychromatic418967fa.accept_17_9_4_2_1_2298 9 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 189 (accept_3_5 8 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 189 (Polychromatic418967fa.accept_20_7_17_9_1_10825 7 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 157 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 189 (accept_3_5 5 157 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 189 (accept_3_5 2 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 157 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 189))))))))))))))))))))))))))))))))) (allB_succ' 34 156 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 156 189 3 11 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 156 189 (Polychromatic418967fa.accept_22_10_2_13_1_5964 32 156 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 31 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 189 3 10 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274 29 156 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 189
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 28 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 156 189 3 9 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 156 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 156 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 189 3 8 52 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 189 (Polychromatic418967fa.accept_17_5_3_2_1_5847 22 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 156 189 3 7 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 189 (Polychromatic418967fa.accept_16_4_12_13_1_990
  20 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 189
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 189 3 6 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 156
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 189 3 5 52 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 189
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 189 3 4 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236
  11 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 189
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 10 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 156 189 3 3 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 156 189 (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 156 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 189
  (Polychromatic418967fa.accept_20_7_16_9_1_4970 7 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 189 3 2 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 156 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 189 3 1 52 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 189
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 2 156 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 156 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 189)))))))))))))))))))))))))))))))))) (allB_succ' 35 155 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 155 189 (accept_3_4 34 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 155 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 155 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 189 (accept_3_4 31 155 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 189
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 29 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 189 (accept_3_4 28 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 189 (accept_3_4 25 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 155 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 155 189 (accept_3_4 22 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 155 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 155 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 189 (accept_3_4 19 155 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 189
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 189 (accept_3_4 16 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 189 (accept_3_4 13 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 155 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 189 (accept_3_4 10 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 189 (Polychromatic418967fa.accept_19_9_3_18_1_5263 9 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 189 (accept_3_4 7 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 189
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 189 (accept_3_4 4 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 155 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 189 (accept_3_4 1 155 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 189))))))))))))))))))))))))))))))))))) (allB_succ' 36 154 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 154 189 7 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 154 189 (Polychromatic418967fa.accept_19_15_2_18_1_6699 34 154 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 189 (Polychromatic418967fa.accept_10_3_4_9_1_15
  33 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 189 (accept_3_5 32
  154 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 154 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 189 (accept_3_5 29 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 154 189 7 4 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 154 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 189 (accept_3_5 26 154 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 154 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 189
  (Polychromatic418967fa.accept_19_5_2_18_1_2716 24 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 189 (accept_3_5 23 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 154 189 7 3 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 154 189 (accept_3_5 20 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 154 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 154
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 189 (accept_3_5 17 154
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 189
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 154 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 189 7 2 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 189
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 154 189 (accept_3_5 11 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 154 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 154
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 189 (accept_3_5 8 154 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 154 189 7 1 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 154 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 6
  154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 189 (accept_3_5 5 154
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 4 154 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 154 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 189 (accept_3_5 2 154 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 154 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 154 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 189)))))))))))))))))))))))))))))))))))) (allB_succ' 37 153 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 153 189 9 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 153 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 153 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 189 3 11 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 189 (Polychromatic418967fa.accept_19_13_1_18_1_5279 32 153 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 189
  (Polychromatic418967fa.accept_19_12_1_18_1_9570 31 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 153 189 3 10 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 153 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 153 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 189 9 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 153 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 153
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 189 3 8 51 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 189 (Polychromatic418967fa.accept_14_8_13_7_1_2798 22 153 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 189 3 7 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 20
  153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 189
  (Polychromatic418967fa.accept_20_19_13_9_1_5019 19 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 153 189 9 2 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 153 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 153 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 189 3 5 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 153 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 153
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 189 3 4 51 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 189
  (Polychromatic418967fa.accept_19_11_1_18_1_5276 11 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 153 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 189 9 1 17 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 189 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 153 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 189 3 2 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 153 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 153 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 189 3 1 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 189 (Polychromatic418967fa.accept_19_2_1_18_1_2660 2 153 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 153 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 189)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 152 189 (Eq.refl Bool.true) (allA_succ_of_accept 37 152 189 (accept_3_4 37 152 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 152 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 152 189 (accept_3_4 34 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 152 189 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 152 189 (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 189 (accept_3_4 31 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 152
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 152 189 (accept_3_4 28 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 152 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 152 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 189 (accept_3_4 25 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 152
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 152 189 (accept_3_4 22 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 152 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 152 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 189 (accept_3_4 19 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 152
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 189 (accept_3_4 16 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 189 (Polychromatic418967fa.accept_17_14_16_2_1_4553 14 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 189 (accept_3_4 13 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 12 152
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 189 (accept_3_4 10 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 189 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 152 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 189 (accept_3_4 7 152 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 152 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 189 (accept_3_4 4 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 152 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 152 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 189 (accept_3_4 1 152 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 189)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 151 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 151 189 (accept_3_5 38 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 151 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 37 151 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 151
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 189 (accept_3_5 35 151
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2
  34 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 189
  (Polychromatic418967fa.accept_22_11_19_13_1_9237 33 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 151 189 (accept_3_5 32 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 151 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 151 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 189 (accept_3_5 29 151 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 189 (accept_3_5 26 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 189 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 189 (accept_3_5 23 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 189
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 189 (accept_3_5 20 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 189 (Polychromatic418967fa.accept_31_19_27_3_1_10985 19 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 189 (accept_3_5 17 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 189 (accept_3_5 14 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 189 (Polychromatic418967fa.accept_17_13_15_2_1_654 13 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 189 (accept_3_5 11 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 189 (accept_3_5 8 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 189 (accept_3_5 5 151 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 189 (accept_3_5 2 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 151 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 189))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 150 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 150 189 3 13 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 150 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 150 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 189 (Polychromatic418967fa.accept_17_3_14_2_1_646
  37 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 189 3 12 50 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 150 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 189 3 11 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 189 3 10 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 189 (Polychromatic418967fa.accept_19_10_17_18_1_9555 29 150 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 189 3 9 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 189 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 150
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 189 3 8 50 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 189 3 7 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  20 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 189 3 6 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 189 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 150
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 189 3 5 50 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 189 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 189 3 4 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 150 189 3 3 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 150 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 189 3 2 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 189
  (Polychromatic418967fa.accept_17_5_14_2_1_4568 5 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 150 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 189 3 1 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 150 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 189
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 150 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 189)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 149 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 149 189 (accept_3_4 40 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 189 (accept_3_4 37 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 149 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 35 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 189 (accept_3_4 34 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 189 (accept_3_4 31 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 189
  (Polychromatic418967fa.accept_22_7_17_13_1_10962 29 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 149 189 (accept_3_4 28 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 149 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 149 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 149 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 189 (accept_3_4 25 149 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 189
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 24 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 149 189 (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 149 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 189 (accept_3_4 22 149 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 149 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 189 (accept_3_4 19 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 189 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 17 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 189 (accept_3_4 16 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 149 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 189 (accept_3_4 13 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 189 (Polychromatic418967fa.accept_22_11_17_13_1_9270 11 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 189 (accept_3_4 10 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 149 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 189 (accept_3_4 7 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 189 (accept_3_4 4 149 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 149 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 189 (accept_3_4 1 149 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  189))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 148 189 (Eq.refl Bool.true) (allA_succ_of_accept 41 148
  189 (accept_3_5 41 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 148 189
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 40 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 148 189 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 148 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 189 (accept_3_5 38 148 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 189
  (Polychromatic418967fa.accept_22_14_16_13_1_10984 36 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 148 189 (accept_3_5 35 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 148 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 148 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 189 (accept_3_5 32 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 189 (accept_3_5 29 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 189 (accept_3_5 26 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 189 (accept_3_5 23 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 22 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 189 (accept_3_5 20 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 189 (accept_3_5 17 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 189 (Polychromatic418967fa.accept_19_16_15_18_1_5252 16 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 189 (accept_3_5 14 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 189
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 189 (accept_3_5 11 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 189 (Polychromatic418967fa.accept_17_10_12_2_1_3385 10 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 148 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 189 (accept_3_5 8 148 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 189 (accept_3_5 5 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 148 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 189 (accept_3_5 2 148 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  189)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 147 189 (Eq.refl Bool.true) (allA_succ_of_gcd 42 147 189
  21 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147
  189 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 147 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 40 147 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 189 3 13 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 189 3 12 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 147 189 7 5 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 147 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 189 3 11 49 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 189 3 10 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 189 (Polychromatic418967fa.accept_12_5_3_9_1_541
  29 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 189 7 4 21 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 147 189 3 9 49 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 189 3 8 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 189 21 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 147
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 189 3 6 49 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 189 3 5 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 147 189 7 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  13 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 189 3 4 49 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 189 3 3 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 147 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 189 7 1 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 147 189 3 2 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 147 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 189 3 1 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 147 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 189))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 146 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 146 189 (accept_3_4 43 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 189 (accept_3_4 40 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 189
  (Polychromatic418967fa.accept_22_16_14_13_1_10858 38 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 146 189 (accept_3_4 37 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 146 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 146 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 189 (accept_3_4 34 146 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 189 (Polychromatic418967fa.accept_10_3_6_9_1_779
  33 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 32 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 189 (accept_3_4 31 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 189 (accept_3_4 28 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 189
  (Polychromatic418967fa.accept_22_4_14_13_1_5977 26 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 146 189 (accept_3_4 25 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 146 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 146 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 189 (accept_3_4 22 146 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  21 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 189
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 189 (accept_3_4 19 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 189 (accept_3_4 16 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 189
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 189 (accept_3_4 13 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 189 (accept_3_4 10 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 146 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 189
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 189 (accept_3_4 7 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 189 (accept_3_4 4 146 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 189 (accept_3_4 1 146 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  189)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 145 189 (Eq.refl Bool.true) (allA_succ_of_accept 44 145
  189 (accept_3_5 44 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 189
  (Polychromatic418967fa.accept_25_18_20_14_1_10983 43 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 42 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 189 (accept_3_5 41 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 145 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 189 (accept_3_5 38 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 145 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 189 (accept_3_5 35 145 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 189
  (Polychromatic418967fa.accept_15_3_10_9_1_769 33 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 189 (accept_3_5 32 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 189 (accept_3_5 29 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 189 (accept_3_5 26 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 189 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 189 (accept_3_5 23 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 145 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 189 (accept_3_5 20 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 189 (accept_3_5 17 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 189 (accept_3_5 14 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 189 (Polychromatic418967fa.accept_19_13_12_18_1_2677 13 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 189 (accept_3_5 11 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 145 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 189 (accept_3_5 8 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 189 (Polychromatic418967fa.accept_17_7_9_2_1_629 7 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 145 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 189 (accept_3_5 5 145 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 189 (accept_3_5 2 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 145 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 189))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 144 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 144 189 9 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 144 189 (Polychromatic418967fa.accept_17_10_8_2_1_8411 44 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 144 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 189 3 14 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 189
  (Polychromatic418967fa.accept_19_3_11_18_1_2709 41 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 144 189 (Polychromatic418967fa.accept_28_12_4_21_1_10982 40 144 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 144 189 3 13 48 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 144 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 189 9 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 189 (Polychromatic418967fa.accept_10_5_4_9_1_420
  35 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 144 189 3 11 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 144 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 144 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 189
  (Polychromatic418967fa.accept_14_3_4_7_1_175 31 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 189 3 10 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 144 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 144 189 9 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 144 189 (Polychromatic418967fa.accept_19_7_11_18_1_6680 26 144 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 189 (Polychromatic418967fa.accept_10_5_4_9_1_420
  25 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 189 3 8 48 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 189 (Polychromatic418967fa.accept_19_3_11_18_1_2709 22 144 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 189 3 7 48 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 189
  (Polychromatic418967fa.accept_19_1_11_18_1_10841 20 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 144 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 144 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 189 9 2 16 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 189
  (Polychromatic418967fa.accept_14_3_4_7_1_175 17 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 189 3 5 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  14 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 13 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 189 3 4 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 144
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 189 9 1 16 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 189 (Polychromatic418967fa.accept_19_7_11_18_1_6680 7 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 189 3 2 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 144 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 189
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 4 144 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 144 189 3 1 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 144 189 (Polychromatic418967fa.accept_20_2_4_9_1_9524 2 144 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 189 (Polychromatic418967fa.accept_19_1_11_18_1_10841 1 144
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  189)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 143 189 (Eq.refl Bool.true) (allA_succ_of_accept 46
  143 189 (accept_3_4 46 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 189
  (Polychromatic418967fa.accept_19_7_10_18_1_6695 45 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 143 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 189 (accept_3_4 43 143 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 189
  (Polychromatic418967fa.accept_22_19_11_13_1_10981 41 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 143 189 (accept_3_4 40 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 143 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 143 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 189 (accept_3_4 37 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 189
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 35 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 143 189 (accept_3_4 34 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 143 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 143 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 189 (accept_3_4 31 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 189
  (Polychromatic418967fa.accept_15_14_8_9_1_1452 29 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 189 (accept_3_4 28 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 189 (accept_3_4 25 143 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 189
  (Polychromatic418967fa.accept_32_23_15_29_1_10980 23 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 143 189 (accept_3_4 22 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 143 189 (Polychromatic418967fa.accept_19_2_10_18_1_6691 21 143 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 189 (accept_3_4 19
  143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 143 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 189 (accept_3_4 16 143 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 143 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 189 (accept_3_4 13 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 189 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 189 (accept_3_4 10 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 189 (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 189 (accept_3_4 7 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 189 (Polychromatic418967fa.accept_19_5_10_18_1_2705 5 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 189 (accept_3_4 4 143 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 143 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 189 (accept_3_4 1 143 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  189))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 142 189 (Eq.refl Bool.true) (allA_succ_of_accept 47
  142 189 (accept_3_5 47 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 189
  (Polychromatic418967fa.accept_15_1_7_9_1_20 46 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 142 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 189 (accept_3_5 44 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 142 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 189 (accept_3_5 41
  142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 189
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 142 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 189 (accept_3_5 38 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 142 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 142 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 142 189 (accept_3_5 35 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 142 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 189 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 142
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 189 (accept_3_5 32 142
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 142 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 189 (accept_3_5 29 142 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 142 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 189 (accept_3_5 26 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 189 (accept_3_5 23 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 189 (Polychromatic418967fa.accept_19_3_9_18_1_10979 22 142
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 21 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 189 (accept_3_5 20 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 189 (accept_3_5 17 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 16 142 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 189 (accept_3_5 14 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 189 (accept_3_5 11 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 142
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 189
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 189 (accept_3_5 8 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 142 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 189 (accept_3_5 5 142 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 142 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 189 (accept_3_5 2 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 142 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 189)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 141 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 141 189 3 16 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 141 189 (Polychromatic418967fa.accept_18_11_15_9_1_360 47 141 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 46 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 141 189 3 15 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 141 189 (Polychromatic418967fa.accept_13_5_11_7_1_559 44 141 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 43 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 189 3 14 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 141 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 40 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 141 189 3 13 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 141 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 38 141 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 189 (Polychromatic418967fa.accept_11_4_9_2_1_259
  37 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 189 3 12 47 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 34 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 189 3 11 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  32 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 31 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 189 3 10 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 141 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 189 (Polychromatic418967fa.accept_10_8_1_9_1_413
  28 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 189 3 9 47 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 189 3 8 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 189 (Polychromatic418967fa.accept_18_5_15_9_1_1919
  23 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 141 189 3 7 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 141 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 141
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 189 3 6 47 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 189 3 5 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704
  14 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 189
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 141 189 3 4 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 189 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 141
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 189 3 3 47 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 189
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 189 3 2 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 141 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 141 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 189 3 1 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 141 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 141
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  189))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 140 189 (Eq.refl Bool.true) (allA_succ_of_gcd 49
  140 189 7 7 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 140 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 48 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 189 (accept_3_4 46 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 189 (Polychromatic418967fa.accept_23_22_2_5_1_10978 45 140 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 189
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 44 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 189 (accept_3_4 43 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  140 189 7 6 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 140 189 (accept_3_4 40 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 140 189 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 140 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 189 (accept_3_4 37 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 189
  (Polychromatic418967fa.accept_16_4_12_13_1_990 36 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 140 189 7 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 140 189 (accept_3_4 34 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 189 (Polychromatic418967fa.accept_17_15_4_2_1_8419 32 140 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 189 (accept_3_4 31 140 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 189 7 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 140 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 189 (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 189 (accept_3_4 25 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 189
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 189 (accept_3_4 22 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 140 189 7 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 140 189 (Polychromatic418967fa.accept_16_4_12_13_1_990 20 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 189 (accept_3_4 19 140
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 189
  (Polychromatic418967fa.accept_12_6_8_9_1_553 18 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 189 (accept_3_4 16 140 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 140 189 (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 140 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 189 7 2 20 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 189 (accept_3_4 13 140 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 189
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 189 (accept_3_4 10 140 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 140 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 140 189 7 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 140 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 140 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 189 (accept_3_4 4 140 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  3 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 189
  (Polychromatic418967fa.accept_22_2_8_13_1_10977 2 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 189 (accept_3_4 1 140 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  189)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 139 189 (Eq.refl Bool.true) (allA_succ_of_accept
  50 139 189 (accept_3_5 50 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 189
  (Polychromatic418967fa.accept_19_11_6_18_1_2717 49 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 189 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 189 (accept_3_5 47 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 189 (accept_3_5 44 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 189 (accept_3_5 41 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 189 (accept_3_5 38 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 189 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 189 (accept_3_5 35 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 189
  (Polychromatic418967fa.accept_20_13_19_9_1_10976 33 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 139 189 (accept_3_5 32 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 139 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 139 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 189 (accept_3_5 29 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 189 (accept_3_5 26 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 189 (accept_3_5 23 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 189
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 189 (accept_3_5 20 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 189 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 189 (accept_3_5 17 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 189 (accept_3_5 14 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 189 (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 189 (accept_3_5 11 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 189 (accept_3_5 8 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 189 (Polychromatic418967fa.accept_19_7_6_18_1_8123 7 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 189 (accept_3_5 5 139 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 189 (accept_3_5 2 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 139 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 189))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 138 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 138 189 3 17 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 138 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 138 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 189
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 189 3 16 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 189 (Polychromatic418967fa.accept_12_10_6_9_1_549
  46 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 138 189 3 15 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 138 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 189 3 14 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 189 (Polychromatic418967fa.accept_10_1_8_9_1_787
  41 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 138 189 3 13 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 138 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 138 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 189 (Polychromatic418967fa.accept_10_7_8_9_1_785
  37 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 138 189 3 12 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 138 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 138 189 3 11 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 138 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 189 3 10 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 138 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 138 189 3 9 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 138 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 138
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 189 3 8 46 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 189 3 7 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 189 3 6 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 138
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 189 3 5 46 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 189 3 4 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 138 189 3 3 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 138 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 189 3 2 46 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 189
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 138 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 189 3 1 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 138 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 1 138 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 189)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 137 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 137 189 (accept_3_4 52 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 189 (accept_3_4 49 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 189
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 47 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 189 (accept_3_4 46 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 189 (accept_3_4 43 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 189 (accept_3_4 40 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 189 (accept_3_4 37 137 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 189
  (Polychromatic418967fa.accept_25_10_12_14_1_10975 35 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 137 189 (accept_3_4 34 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 137 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 137 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 189 (accept_3_4 31 137 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  30 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 189
  (Polychromatic418967fa.accept_23_6_22_5_1_10974 29 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 137 189 (accept_3_4 28 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 137 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 137 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 137 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 189 (accept_3_4 25 137 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 189
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 189 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 189 (accept_3_4 22 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 137
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 189 (accept_3_4 19 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 189 (accept_3_4 16 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 137
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 189 (accept_3_4 13 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 189 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 189 (accept_3_4 10 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 189 (Polychromatic418967fa.accept_25_9_12_14_1_10949 9 137
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 189 (accept_3_4 7 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 189 (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 189 (accept_3_4 4 137 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 137 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 189 (accept_3_4 1 137 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  189))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 136 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 136 189 (accept_3_5 53 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 52 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 189 (accept_3_5 50 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 136 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 189 (accept_3_5 47 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 189 (Polychromatic418967fa.accept_14_4_10_7_1_1946 46 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 189 (accept_3_5 44 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 42 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 189 (accept_3_5 41 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 189 (accept_3_5 38 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 189
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 189 (accept_3_5 35 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 189 (Polychromatic418967fa.accept_19_15_3_18_1_5241 34 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 189 (accept_3_5 32 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 189 (accept_3_5 29 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 189 (accept_3_5 26 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 189
  (Polychromatic418967fa.accept_22_2_4_13_1_10973 24 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 136 189 (accept_3_5 23 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 136 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 136 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 136
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 189 (accept_3_5 20 136
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 136 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 136 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 189 (accept_3_5 17 136 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 136 189 (Polychromatic418967fa.accept_19_16_3_18_1_8120 16 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 189 (accept_3_5 14 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 189 (accept_3_5 11 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 189 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 136
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 189 (accept_3_5 8 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 136 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 189 (accept_3_5 5 136 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 136 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 3 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 189 (accept_3_5 2 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 189)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 135 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 135 189 27 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 135 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 135 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 189
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 52 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 135 189 3 17 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 135 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  49 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 189 3 16 45 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 189 9 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  44 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 189 3 14 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 135 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 189
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 135 189 3 13 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  37 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 189 9 4 15 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 189 3 11 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 189
  (Polychromatic418967fa.accept_22_10_3_13_1_10972 32 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 135 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 189 3 10 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 189 27 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 135 189 3 8 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 189 3 7 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 189
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 189 9 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 189 (Polychromatic418967fa.accept_12_5_3_9_1_541
  17 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 189
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 189 3 5 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 135
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 189 3 4 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 189 9 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 189 (Polychromatic418967fa.accept_17_8_16_2_1_10847 8 135
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 189 3 2 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 135 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 189 3 1 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 135 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 189))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 134 189 (Eq.refl Bool.true) (allA_succ_of_accept 55 134 189 (accept_3_4 55 134 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 134 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 134 189 (accept_3_4 52 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 134 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 134 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 134 189 (accept_3_4 49 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 134 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 134 189 (accept_3_4 46 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 134 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 189 (Polychromatic418967fa.accept_17_10_15_2_1_653 44 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 189 (accept_3_4 43 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 189 (accept_3_4 40 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 189 (accept_3_4 37 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 189 (accept_3_4 34 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 189 (accept_3_4 31 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 189 (accept_3_4 28 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 189 (Polychromatic418967fa.accept_19_7_1_18_1_2691 26 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 189 (accept_3_4 25 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 189 (accept_3_4 22 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 189 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 189 (accept_3_4 19 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 189 (accept_3_4 16 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 189 (Polychromatic418967fa.accept_19_14_1_18_1_5280 14 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 189 (accept_3_4 13 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 134
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 189 (accept_3_4 10 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 189 (accept_3_4 7 134 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 189 (accept_3_4 4 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 189 (Polychromatic418967fa.accept_19_2_1_18_1_2660 2 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 189 (accept_3_4 1 134 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 134 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  57 133 189 (Eq.refl Bool.true) (allA_succ_of_gcd 56 133 189 7 8 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 133 189 (Polychromatic418967fa.accept_24_7_13_21_1_10971 55 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 189 (accept_3_5 53 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 189 (accept_3_5 50 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 133 189 7 7 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 133 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065
  48 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 189 (accept_3_5 47
  133 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 189
  (Polychromatic418967fa.accept_6_4_1_3_1_77 46 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 133 189 (Polychromatic418967fa.accept_25_20_8_14_1_9091 45 133 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 189 (accept_3_5 44 133 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 133 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 133 189 7 6 19 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 133 189 (accept_3_5 41
  133 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 189
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 133 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 189 (accept_3_5 38 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 133 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 133 189 7 5 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 133 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 189 (accept_3_5 32 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 189
  (Polychromatic418967fa.accept_22_9_1_13_1_7731 31 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 133 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 189 (accept_3_5 29 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 133 189 7 4 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 133 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 189 (accept_3_5 26 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 189 (accept_3_5 23 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 133 189 7 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 133 189 (accept_3_5 20 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 133 189 (Polychromatic418967fa.accept_15_4_13_9_1_3197 19 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 189 (accept_3_5 17 133
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 189
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 133 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 133 189 7 2 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 133 189
  (Polychromatic418967fa.accept_23_13_18_5_1_10970 13 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 189 (Polychromatic418967fa.accept_22_12_1_13_1_1623 12 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 189 (accept_3_5 11 133 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 133 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 189
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 189 (accept_3_5 8 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133
  189 7 1 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  133 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 133 189 (accept_3_5 5 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 133 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 133 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 189 (accept_3_5 2 133 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  1 133 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 132 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 132 189 3 19 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 132 189 (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 189
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 55 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 189 3 18 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 189 (Polychromatic418967fa.accept_26_1_2_7_1_10969 53 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 189
  (Polychromatic418967fa.accept_17_1_13_2_1_7086 52 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 132 189 3 17 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 132 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 50 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 189 3 16 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 132 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 189
  (Polychromatic418967fa.accept_25_21_7_14_1_10968 46 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 132 189 3 15 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 132 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 44 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 189
  (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 189 3 14 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 132 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 40 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 132 189 3 13 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 132 189 (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 189
  (Polychromatic418967fa.accept_10_7_2_9_1_775 37 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 189 3 12 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 189
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 34 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 132 189 3 11 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 132 189 (Polychromatic418967fa.accept_17_15_13_2_1_3418 32 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 31 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 189 3 10 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 189 (Polychromatic418967fa.accept_14_1_6_7_1_1936 29 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 189
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 132 189 3 9 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 132 189 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 132 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 189 3 8 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 189 (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 132 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 132
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 189 3 7 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 189
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 132 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 189 3 6 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 17
  132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 189
  (Polychromatic418967fa.accept_28_16_20_21_1_10967 16 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 132 189 3 5 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 132 189 (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 132 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 189
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 189 3 4 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 132 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 10 132
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 189 3 3 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 189
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 132 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 189 3 2 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 132 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 132 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 132 189 3 1 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 132 189 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 132 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 132 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 131 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 131 189 (accept_3_4 58 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 189 (Polychromatic418967fa.accept_17_6_12_2_1_10966 57 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 189 (accept_3_4 55 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 189
  (Polychromatic418967fa.accept_22_9_21_13_1_10830 53 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 131 189 (accept_3_4 52 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 131 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 131 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 189 (accept_3_4 49 131 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 189 (Polychromatic418967fa.accept_10_8_1_9_1_413
  48 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 189 (accept_3_4 46 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 189 (accept_3_4 43 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 189
  (Polychromatic418967fa.accept_17_7_12_2_1_7105 41 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 189 (accept_3_4 40 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 189 (accept_3_4 37 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 131 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 189 (accept_3_4 34 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 189 (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 189 (accept_3_4 31 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 189
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 189 (accept_3_4 28 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 189 (accept_3_4 25 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 131 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 189 (accept_3_4 22 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 189 (accept_3_4 19 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 17 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 189 (accept_3_4 16 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 189 (accept_3_4 13 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 189
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 189 (accept_3_4 10 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 189 (accept_3_4 7 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 189 (accept_3_4 4 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 131 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 189 (accept_3_4 1 131 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 130
  189 (Eq.refl Bool.true) (allA_succ_of_accept 59 130 189 (accept_3_5 59 130 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 130 189 (Polychromatic418967fa.accept_31_27_6_3_1_10965 58 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 57 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 189 (accept_3_5 56 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 189 (accept_3_5 53 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 189 (accept_3_5 50 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 189 (accept_3_5 47 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 189 (Polychromatic418967fa.accept_15_1_10_9_1_1495 46 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 189
  (Polychromatic418967fa.accept_14_3_4_7_1_175 45 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 189 (accept_3_5 44 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 189 (accept_3_5 41 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 189 (accept_3_5 38 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 189 (Polychromatic418967fa.accept_19_17_16_18_1_2684 36 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 189 (accept_3_5 35 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 189
  (Polychromatic418967fa.accept_15_3_10_9_1_769 33 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 189 (accept_3_5 32 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 189 (accept_3_5 29 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 189 (Polychromatic418967fa.accept_19_9_16_18_1_3887 28 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 189 (accept_3_5 26 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 189 (accept_3_5 23 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 189 (Polychromatic418967fa.accept_19_3_16_18_1_2683 22 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 189
  (Polychromatic418967fa.accept_16_5_2_13_1_1007 21 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 189 (accept_3_5 20 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 189 (accept_3_5 17 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 189 (Polychromatic418967fa.accept_15_1_10_9_1_1495 16 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 189 (accept_3_5 14 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 189 (accept_3_5 11 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 130
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 189
  (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 189 (accept_3_5 8 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 130 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 189 (accept_3_5 5 130 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 130 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 189 (accept_3_5 2 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 130 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 129 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 129 189 3 20 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 189 (Polychromatic418967fa.accept_17_8_10_2_1_4546 59 129
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 58 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 189 3 19 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 189
  (Polychromatic418967fa.accept_18_1_3_9_1_328 55 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 129 189 3 18 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 129 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 52 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 129 189 3 17 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 129 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 189 3 16 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 189
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 46 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 189 3 15 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 129 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 189
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 189 3 14 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 189 (Polychromatic418967fa.accept_16_9_1_13_1_1850 41 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 189
  (Polychromatic418967fa.accept_19_2_15_18_1_1556 40 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 129 189 3 13 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 129 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 189
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 129 189 3 12 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 129 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 189
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 189 3 11 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 189
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 189 3 10 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 189 (Polychromatic418967fa.accept_17_12_10_2_1_5835 29 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 189 3 9 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 189 (Polychromatic418967fa.accept_18_8_3_9_1_4232 26 129 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 129
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 189 3 8 43 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 189 (Polychromatic418967fa.accept_19_3_15_18_1_2682 22 129 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 189 3 7 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 129 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 189 3 6 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439
  17 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 16 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 189 3 5 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 189 (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 129 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 189
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 189 3 4 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 129 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 129 189 3 3 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 129 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 129 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 189 (Polychromatic418967fa.accept_18_7_3_9_1_1020
  7 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 189 3 2 43 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 129 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 189 3 1 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 2 129 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 189
  (Polychromatic418967fa.accept_18_1_3_9_1_328 1 129 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 128 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 189 (accept_3_4 61 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 128 189 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 128 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 128 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 128 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 189 (accept_3_4 58 128 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 189 (Polychromatic418967fa.accept_10_7_8_9_1_785
  57 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 56 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 128 189 (accept_3_4 55 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 128 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 128 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 128 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 189 (accept_3_4 52 128 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 189
  (Polychromatic418967fa.accept_22_6_18_13_1_10907 50 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 128 189 (accept_3_4 49 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 128 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 128 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 189 (accept_3_4 46 128 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 189
  (Polychromatic418967fa.accept_17_11_9_2_1_8423 45 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 128 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 128 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 189 (accept_3_4 43 128 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 128 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 189 (accept_3_4 40 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 189 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 38 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 189 (accept_3_4 37 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 189 (Polychromatic418967fa.accept_22_14_18_13_1_10864 36
  128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 189 (accept_3_4 34 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 189 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 189 (accept_3_4 31 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 128
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 189 (accept_3_4 28 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 189 (accept_3_4 25 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 128
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 189 (accept_3_4 22 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 189 (accept_3_4 19 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 128
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 189 (accept_3_4 16 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 189 (Polychromatic418967fa.accept_19_15_14_18_1_6696 15 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 189 (accept_3_4 13 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 128
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 189 (accept_3_4 10 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 189 (Polychromatic418967fa.accept_23_8_13_5_1_10964 8 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 189 (accept_3_4 7 128 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 128 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 189 (accept_3_4 4 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 128 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2 128 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 189 (accept_3_4 1 128 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  127 189 (Eq.refl Bool.true) (allA_succ_of_accept 62 127 189 (accept_3_5 62 127 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 127 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 61 127 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 189 (accept_3_5 59 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 189 (Polychromatic418967fa.accept_18_3_1_9_1_1929 57 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 189 (accept_3_5 56 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 127
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 189 (accept_3_5 53 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 189 (accept_3_5 50 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 189 (Polychromatic418967fa.accept_34_15_25_19_1_10963 49
  127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 189
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 189 (accept_3_5 47 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 189 (accept_3_5 44 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 127
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 189 (accept_3_5 41 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 189 (accept_3_5 38 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 127 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 189
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 189 (accept_3_5 35 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 189 (Polychromatic418967fa.accept_17_16_8_2_1_5890 33 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 189 (accept_3_5 32 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 31 127 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 189 (accept_3_5 29 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 189 (accept_3_5 26 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 127
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 189
  (Polychromatic418967fa.accept_18_6_1_9_1_5551 24 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 189 (accept_3_5 23 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 189 (accept_3_5 20 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 189 (Polychromatic418967fa.accept_16_3_15_13_1_2825 19 127
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 189 (accept_3_5 17 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 127 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 189 (accept_3_5 14 127 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 127 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 189 (accept_3_5 11 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 189 (Polychromatic418967fa.accept_19_9_13_18_1_10812 9 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 189 (accept_3_5 8 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 189 (Polychromatic418967fa.accept_22_7_17_13_1_10962 7 127
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 189 (accept_3_5 5 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 127 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 189 (accept_3_5 2 127 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 127 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 126 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 126 189 63 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 126 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 61 126
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 189 3 20 42 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 126 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 126 189 3 19 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 189 7 8 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 189 9 6 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 53 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 126 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 126 189 3 17 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 126 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 126 189 7 7 18 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 189 3 16 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 126 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 126 189 9 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 126 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 189 21 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 126
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 126 189 3 13 42 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 126 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 189 9 4 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 189 7 5 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 126 189 (Polychromatic418967fa.accept_12_10_6_9_1_549
  34 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 189 3 11 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 189 3 10 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730
  29 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 189 7 4 18 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 189 9 3 14 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 126 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 189 3 8 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 126 189 21 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 126 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 189 9 2 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 189
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 189 3 5 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 189 7 2 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 189 (Polychromatic418967fa.accept_10_3_6_9_1_779
  13 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 189 3 4 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 189 9 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 126 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 126 189 7 1 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 189 3 2 42 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 126 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 189 3 1 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 126 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 126 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 125 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 125 189 (accept_3_4 64 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 125 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 125 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 189 (accept_3_4 61 125 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 189
  (Polychromatic418967fa.accept_19_3_11_18_1_2709 60 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 189 (Polychromatic418967fa.accept_15_14_5_9_1_2284 59 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 189 (accept_3_4 58 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 189 (accept_3_4 55 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 189 (accept_3_4 52 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 189 (accept_3_4 49 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 189 (Polychromatic418967fa.accept_17_13_6_2_1_5850 47 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 189 (accept_3_4 46 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 189 (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 189 (accept_3_4 43 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 189 (accept_3_4 40 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 189 (accept_3_4 37 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 189 (accept_3_4 34 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 189 (accept_3_4 31 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 189 (Polychromatic418967fa.accept_17_13_6_2_1_5850 30 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 189 (accept_3_4 28 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 189 (accept_3_4 25 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 189 (accept_3_4 22 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 189 (accept_3_4 19 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 189 (accept_3_4 16 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 125
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 189 (accept_3_4 13 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 189 (accept_3_4 10 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 125 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 189 (accept_3_4 7 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 189 (Polychromatic418967fa.accept_26_5_21_7_1_10961 5 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 189 (accept_3_4 4 125 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 125 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 189 (accept_3_4 1 125 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 124 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 124 189 (accept_3_5 65 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 189 (Polychromatic418967fa.accept_19_7_10_18_1_6695 64 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 124 189 (accept_3_5 62 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 189
  (Polychromatic418967fa.accept_22_16_14_13_1_10858 60 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 124 189 (accept_3_5 59 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 124 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 124 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 189 (accept_3_5 56 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 189 (accept_3_5 53 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 189 (Polychromatic418967fa.accept_16_4_12_13_1_990 52 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 189 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 189 (accept_3_5 50 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 124 189 (accept_3_5 47 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 124 189 (Polychromatic418967fa.accept_19_8_10_18_1_5232 46 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 124 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 189 (accept_3_5 44 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 124 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 124 189 (accept_3_5 41 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 124 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 40 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 124 189 (Polychromatic418967fa.accept_20_19_4_9_1_5025 39 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 189 (accept_3_5 38 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 124 189
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 124 189 (accept_3_5 35 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 189 (accept_3_5 32 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 189 (accept_3_5 29 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 189 (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 189 (accept_3_5 26 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 189
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 124 189 (accept_3_5 23 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 124 189 (Polychromatic418967fa.accept_20_2_4_9_1_9524 22 124 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 189 (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 124
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 189 (accept_3_5 20 124
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 124 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 124 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 189 (accept_3_5 17 124 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 124 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 189
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 189 (accept_3_5 14 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 189 (accept_3_5 11 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 124
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 189 (accept_3_5 8 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 189 (accept_3_5 5 124 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 189 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 124 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 189 (accept_3_5 2 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 123 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 123 189 3 22 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 123 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 123 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 189 3 21 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 123 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  61 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 189 3 20 41 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 189 3 19 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  56 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 55 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 189 3 18 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 123 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 189
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 52 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 123 189 3 17 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 189 3 16 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 123 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 189 3 15 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 123 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 189 3 14 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 123 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 189 (Polychromatic418967fa.accept_13_1_6_7_1_550
  40 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 189 3 13 41 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 189 3 12 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 189 3 11 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 189 (Polychromatic418967fa.accept_14_4_11_7_1_1234 32 123 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 189 3 10 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 123 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 189 3 9 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 123
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 189 3 8 41 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 189 3 7 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 189 (Polychromatic418967fa.accept_15_5_3_9_1_283
  20 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 123 189 3 6 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 123 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 123
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 189 3 5 41 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 189 3 4 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 123 189 3 3 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 123 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 123 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 189 3 2 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 123 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 189 3 1 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 123 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 122 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 189 (accept_3_4 67 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 122 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 122 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 189 (accept_3_4 64 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 189
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 62 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 122 189 (accept_3_4 61 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 122 189 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 122 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 189 (accept_3_4 58 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 189 (Polychromatic418967fa.accept_10_7_2_9_1_775
  57 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 56 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 189 (accept_3_4 55 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 189 (accept_3_4 52 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 50 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 189 (accept_3_4 49 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 189 (Polychromatic418967fa.accept_17_14_3_2_1_5848 48 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 189 (accept_3_4 46 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 189 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 189
  (Polychromatic418967fa.accept_16_12_10_13_1_1042 44 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 122 189 (accept_3_4 43 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 122 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 122 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 189 (accept_3_4 40 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 189
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 189 (accept_3_4 37 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 189 (accept_3_4 34 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 189 (Polychromatic418967fa.accept_20_13_2_9_1_4958 33 122 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 189 (accept_3_4 31 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 189 (accept_3_4 28 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 189 (accept_3_4 25 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 189 (accept_3_4 22 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 189
  (Polychromatic418967fa.accept_19_1_8_18_1_6667 20 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 189 (accept_3_4 19 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 189 (accept_3_4 16 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 189 (accept_3_4 13 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 189 (accept_3_4 10 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 189 (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 189
  (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 189 (accept_3_4 7 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 189 (accept_3_4 4 122 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 189
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 189 (accept_3_4 1 122 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 121 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 121 189 (accept_3_5 68 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 67 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 66 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 189 (accept_3_5 65 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 189 (accept_3_5 62 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 189 (accept_3_5 59 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 189
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 57 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 189 (accept_3_5 56 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 189 (accept_3_5 53 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 189 (accept_3_5 50 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 189 (accept_3_5 47 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 189 (accept_3_5 44 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 189 (Polychromatic418967fa.accept_25_18_21_14_1_10960 43 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 189 (accept_3_5 41 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 189 (accept_3_5 38 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 189 (accept_3_5 35 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 33 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 189 (accept_3_5 32 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 189 (Polychromatic418967fa.accept_19_12_7_18_1_8110 31 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 189 (accept_3_5 29 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 189 (accept_3_5 26 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 189 (accept_3_5 23 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 189
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 189 (accept_3_5 20 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 189 (accept_3_5 17 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 189 (accept_3_5 14 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 189 (Polychromatic418967fa.accept_24_13_1_21_1_10818 13 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 189 (accept_3_5 11 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 121 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 189
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 189 (accept_3_5 8 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 189 (accept_3_5 5 121 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 189 (accept_3_5 2 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 121 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 120
  189 (Eq.refl Bool.true) (allA_succ_of_gcd 69 120 189 3 23 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 120 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 68 120
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 67 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 189 3 22 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 189 (Polychromatic418967fa.accept_18_11_12_9_1_992 65 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 189
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 64 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 120 189 3 21 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 120 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 62 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 189
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 189 3 20 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 189 (Polychromatic418967fa.accept_16_11_8_13_1_3844 59 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 189
  (Polychromatic418967fa.accept_18_4_12_9_1_2011 58 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 120 189 3 19 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 120 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 120 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 189
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 55 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 189 3 18 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710 53 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 189
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 52 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 120 189 3 17 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 120 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 50 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 189 3 16 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 189
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 46 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 120 189 3 15 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 120 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 120 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 189 3 14 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 189 (Polychromatic418967fa.accept_14_13_8_7_1_1224 41 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 189
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 120 189 3 13 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 120 189 (Polychromatic418967fa.accept_31_7_27_3_1_10959 38 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 189 3 12 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 34 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 120 189 3 11 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 120 189 (Polychromatic418967fa.accept_25_7_20_14_1_10958 32 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 189
  (Polychromatic418967fa.accept_19_12_6_18_1_8095 31 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 120 189 3 10 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 120 189 (Polychromatic418967fa.accept_14_1_8_7_1_1253 29 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 189
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 120 189 3 9 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 120 189 (Polychromatic418967fa.accept_19_7_6_18_1_8123 26 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 189
  (Polychromatic418967fa.accept_22_3_10_13_1_9286 25 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 120 189 3 8 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 120 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 189
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 22 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 120 189 3 7 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 120 189 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 120 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 189 (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 120
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 189 3 6 40 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 189 (Polychromatic418967fa.accept_17_16_1_2_1_3403 16 120 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 189 3 5 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  14 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 189
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 189 3 4 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 120 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 120 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 120
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 189 3 3 40 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 189
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 189 (Polychromatic418967fa.accept_19_7_6_18_1_8123 7 120 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 189 3 2 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 189 (Polychromatic418967fa.accept_16_5_8_13_1_2764 5 120 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 120 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 120 189 3 1 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 120 189 (Polychromatic418967fa.accept_22_2_10_13_1_10888 2 120 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 120 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 119 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 119 189 7 10 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 119 189 (Polychromatic418967fa.accept_18_15_11_9_1_4256 69 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 189 (accept_3_4 67 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 189 (Polychromatic418967fa.accept_15_5_14_9_1_274 65 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 189 (accept_3_4 64 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 119 189 7 9 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62
  119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 189 (accept_3_4 61
  119 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 189
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 119 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 59 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 189 (accept_3_4 58 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 119 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 119 189 7 8 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 119 189 (accept_3_4 55 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 189
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 53 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 189 (accept_3_4 52 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 119 189 7 7 17 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 119 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 189 (accept_3_4 46 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 189 (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 189 (accept_3_4 43 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  119 189 7 6 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 119 189 (Polychromatic418967fa.accept_16_9_7_13_1_4997 41 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 189 (accept_3_4 40 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 189 (accept_3_4 37 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 189
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 119 189 7 5 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 119 189 (accept_3_4 34 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 189 (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 189 (accept_3_4 31 119 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 189 7 4 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 189 (accept_3_4 25 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 189
  (Polychromatic418967fa.accept_20_4_19_9_1_7961 24 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 189 (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 189 (accept_3_4 22 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 119 189 7 3 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 119 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 189 (accept_3_4 19 119 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 189
  (Polychromatic418967fa.accept_19_17_5_18_1_6646 17 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 119 189 (accept_3_4 16 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 119 189 7 2 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 119 189 (accept_3_4 13 119 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 189
  (Polychromatic418967fa.accept_22_11_9_13_1_10928 11 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 189 (accept_3_4 10 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 189 7 1 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 189 (accept_3_4 4 119 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 119 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  119 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 189 (accept_3_4 1 119
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 118 189 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 118 189 (accept_3_5 71 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 189 (Polychromatic418967fa.accept_25_20_18_14_1_10957 70 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 118 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 69 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 189 (accept_3_5 68 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 66 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 189 (accept_3_5 65 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 189 (accept_3_5 62 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 60 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 189 (accept_3_5 59 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 58 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 189 (accept_3_5 56 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 189 (accept_3_5 53 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 189 (accept_3_5 50 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 189
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 48 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 189 (accept_3_5 47 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 189 (Polychromatic418967fa.accept_19_8_4_18_1_5283 46 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 189 (accept_3_5 44 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 189 (accept_3_5 41 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 189 (Polychromatic418967fa.accept_19_2_4_18_1_9556 40 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 189 (accept_3_5 38 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 189
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 189 (accept_3_5 35 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 189 (accept_3_5 32 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 189 (accept_3_5 29 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 189 (Polychromatic418967fa.accept_25_3_18_14_1_10956 28 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 189 (accept_3_5 26 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 189 (accept_3_5 23 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 189 (accept_3_5 20 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 189 (accept_3_5 17 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 189 (accept_3_5 14 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 118 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 189
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 118 189 (accept_3_5 11 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 118 189 (Polychromatic418967fa.accept_23_10_3_5_1_10880 10 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 189 (Polychromatic418967fa.accept_16_9_6_13_1_3831
  9 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 189 (accept_3_5 8
  118 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 118 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 118 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 189 (accept_3_5 5 118 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 118 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 118 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 189 (accept_3_5 2 118
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 189 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 118 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 117 189 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 117 189 9 8 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 117 189 (Polychromatic418967fa.accept_19_14_3_18_1_6675 71 117 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 70 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 117 189 3 23 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 117 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 68 117 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 189
  (Polychromatic418967fa.accept_20_7_17_9_1_10825 67 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 117 189 3 22 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 117 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 65 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 189 9 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 62 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 189 (Polychromatic418967fa.accept_17_10_15_2_1_653 61 117
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 189 3 20 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 189
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 59 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 117 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 58 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 189 3 19 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 189
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 55 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 189 9 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  53 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 52 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 117 189 3 17 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 117 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 50 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 49 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 189 3 16 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 189 (Polychromatic418967fa.accept_17_13_15_2_1_654 47 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 189
  (Polychromatic418967fa.accept_20_6_17_9_1_7975 46 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 189 9 5 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 117 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 189 (Polychromatic418967fa.accept_22_21_7_13_1_10883 43
  117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 189 3 14 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 189
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 189 (Polychromatic418967fa.accept_14_12_5_7_1_2010 40 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 189 3 13 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 189 (Polychromatic418967fa.accept_10_8_7_9_1_425
  38 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 189
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 189 9 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 34 117
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 189 3 11 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 189 3 10 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 189
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 189 9 3 13 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 189
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 189 3 8 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251
  23 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 22 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 117 189 3 7 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 117 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 117
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 189 9 2 13 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 189
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 189 3 5 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 189
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 189 (Polychromatic418967fa.accept_17_13_15_2_1_654 13 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 189 3 4 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 189
  (Polychromatic418967fa.accept_19_11_3_18_1_10828 11 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 117 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 10 117 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 189 9 1 13 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 189
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 189 (Polychromatic418967fa.accept_17_7_15_2_1_10843 7 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 189 3 2 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 117 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 117 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 189 3 1 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 117 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 189 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 117
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 116 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 189 (accept_3_4 73 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 116 189 (Polychromatic418967fa.accept_16_8_4_13_1_1014 72 116 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 116 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 116 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 116 189 (accept_3_4 70 116 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 116 189
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 116 189 (Polychromatic418967fa.accept_23_22_1_5_1_10875 68 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 116 189 (accept_3_4 67 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 116 189 (accept_3_4 64 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 116 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 116 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 62 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 189 (accept_3_4 61 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 189 (accept_3_4 58 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 189 (accept_3_4 55 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 189 (accept_3_4 52 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 51 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 189 (accept_3_4 49 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 116 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 189 (accept_3_4 46 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 44 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 189 (accept_3_4 43 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 189 (accept_3_4 40 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 189 (Polychromatic418967fa.accept_14_11_4_7_1_609 39 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 189 (accept_3_4 37 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 189 (accept_3_4 34 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 189 (accept_3_4 31 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 189 (accept_3_4 28 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 189 (Polychromatic418967fa.accept_20_7_16_9_1_4970 27 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 189 (accept_3_4 25 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 116 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 189 (accept_3_4 22 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 189 (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 189 (accept_3_4 19 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 189 (accept_3_4 16 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 189 (Polychromatic418967fa.accept_22_14_6_13_1_10881 14 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 189 (accept_3_4 13 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 189 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 116
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 189 (accept_3_4 10 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 189 (accept_3_4 7 116 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 116 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 189 (accept_3_4 4 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 116 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 189 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 189 (accept_3_4 1 116 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 75 115 189 (Eq.refl Bool.true) (allA_succ_of_accept 74 115 189 (accept_3_5 74 115 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 189 (Polychromatic418967fa.accept_25_23_15_14_1_10955 73 115 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 72 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 189 (accept_3_5 71 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 69 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 189 (accept_3_5 68 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 67 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 189 (accept_3_5 65 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 189 (accept_3_5 62 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 189
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 189 (accept_3_5 59 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 189 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 189 (accept_3_5 56 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 189 (accept_3_5 53 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 189 (accept_3_5 50 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 49 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 189
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 189 (accept_3_5 47 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 189 (Polychromatic418967fa.accept_19_7_1_18_1_2691 45 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 189 (accept_3_5 44 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 189 (accept_3_5 41 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 189 (accept_3_5 38 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 189 (Polychromatic418967fa.accept_44_37_27_13_1_10954 37
  115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 189
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 189 (accept_3_5 35 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 189 (Polychromatic418967fa.accept_15_3_10_9_1_769 33 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 189 (accept_3_5 32 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 189 (accept_3_5 29 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 189 (accept_3_5 26 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 189 (accept_3_5 23 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 189 (accept_3_5 20 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 189 (accept_3_5 17 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 189 (accept_3_5 14 115 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 189 (Polychromatic418967fa.accept_19_13_1_18_1_5279 13 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 189
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 115 189 (accept_3_5 11 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 115
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 189 (accept_3_5 8 115 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 189
  (Polychromatic418967fa.accept_17_7_13_2_1_10840 7 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 115 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 189 (accept_3_5 5 115 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 115 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  3 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 189 (accept_3_5 2
  115 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 115 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 115 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 114 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 189 3 25 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 114 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 74 114 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 73 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 189 3 24 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 114 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 189 (Polychromatic418967fa.accept_12_10_6_9_1_549
  70 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 114 189 3 23 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 114 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 114 189 3 22 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 114 189 (Polychromatic418967fa.accept_10_5_4_9_1_420
  65 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 64 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 114 189 3 21 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 114 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 114 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 189 (Polychromatic418967fa.accept_11_6_4_2_1_599
  61 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 189 3 20 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 114 189 3 19 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 114 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 189 3 18 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 114 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 189 (Polychromatic418967fa.accept_12_4_6_9_1_548
  52 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 114 189 3 17 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 114 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 189 (Polychromatic418967fa.accept_18_13_6_9_1_4280 49 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 189 3 16 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 114 189 3 15 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 114 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 114 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 189 3 14 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 189 (Polychromatic418967fa.accept_17_7_12_2_1_7105 41 114 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 114 189 3 13 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 114 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 114 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 189
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 37 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 189 3 12 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 189 (Polychromatic418967fa.accept_12_10_6_9_1_549
  34 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 189 3 11 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 189 3 10 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  29 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 114 189 3 9 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 114 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 114
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 189 3 8 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 189 3 7 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 189 (Polychromatic418967fa.accept_11_9_4_2_1_600
  20 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 189 3 6 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 114
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 189 3 5 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 189 3 4 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 114 189 3 3 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 114 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 189 3 2 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 189
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 114 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 189 3 1 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 114 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 189
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 114 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 113 189
  (Eq.refl Bool.true) (allA_succ_of_accept 76 113 189 (accept_3_4 76 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 113 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 113 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 189 (accept_3_4 73 113 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 189
  (Polychromatic418967fa.accept_23_3_21_5_1_10953 72 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 189 (Polychromatic418967fa.accept_13_6_9_7_1_2430 71 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 189 (accept_3_4 70 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 189 (accept_3_4 67 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 66 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 189 (Polychromatic418967fa.accept_23_19_21_5_1_10870 65 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 189 (accept_3_4 64 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 189 (accept_3_4 61 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 189 (Polychromatic418967fa.accept_15_14_8_9_1_1452 59 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 189 (accept_3_4 58 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 189 (Polychromatic418967fa.accept_16_9_1_13_1_1850 57 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 189 (accept_3_4 55 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 189 (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 189 (accept_3_4 52 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 189 (accept_3_4 49 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 189 (accept_3_4 46 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 189 (accept_3_4 43 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 41 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 189 (accept_3_4 40 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 189 (accept_3_4 37 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 189 (accept_3_4 34 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 189 (accept_3_4 31 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 189 (accept_3_4 28 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 189 (accept_3_4 25 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 189 (accept_3_4 22 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 189 (accept_3_4 19 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 189 (accept_3_4 16 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 189 (accept_3_4 13 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 189 (accept_3_4 10 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 189 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 113
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 189 (accept_3_4 7 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 189 (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 189 (accept_3_4 4 113 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 113 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 189 (accept_3_4 1 113 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 112 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 112 189 7 11 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 112 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 76 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 189
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 75 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 189 (accept_3_5 74 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 189 (Polychromatic418967fa.accept_23_3_20_5_1_10952 72 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 189 (accept_3_5 71 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 189 7 10 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 189 (Polychromatic418967fa.accept_18_15_4_9_1_4204
  69 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 189 (accept_3_5 68
  112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 112 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 112 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 66 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 189 (accept_3_5 65 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 112 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 112 189 7 9 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 112 189 (accept_3_5 62 112 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61
  112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 189
  (Polychromatic418967fa.accept_22_16_2_13_1_10951 60 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 112 189 (accept_3_5 59 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 112 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 58 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 112
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 189 7 8 16 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 112 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 54 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 189 (accept_3_5 53 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 112 189 (Polychromatic418967fa.accept_22_8_2_13_1_10950 52 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 51 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 189 (accept_3_5 50 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49
  112 189 7 7 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 112 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 112 189 (accept_3_5 47 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 112 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 189 (Polychromatic418967fa.accept_19_7_17_18_1_8155 45 112
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 189 (accept_3_5 44 112
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 189 7 6 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 112 189 (accept_3_5 41 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 189 (Polychromatic418967fa.accept_19_1_17_18_1_8101 39 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 189 (accept_3_5 38 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 189
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 112 189 7 5 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 112 189 (Polychromatic418967fa.accept_25_9_12_14_1_10949 34 112 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 189
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 33 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 189 (accept_3_5 32 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 189 (accept_3_5 29 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 189 7 4 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 189 (Polychromatic418967fa.accept_10_7_2_9_1_775
  27 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 189 (accept_3_5 26
  112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 112 189 (Polychromatic418967fa.accept_19_5_17_18_1_2686 24 112 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 189 (accept_3_5 23 112 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 112 189 7 3 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 112 189 (accept_3_5 20 112 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 189 (accept_3_5 17 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 189 7 2 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 112 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 189 (accept_3_5 11 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 112 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 112 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 189 (accept_3_5 8 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 112
  189 7 1 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  112 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 112 189 (accept_3_5 5 112 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 112 189 (Polychromatic418967fa.accept_19_4_17_18_1_9536 4 112 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 112 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 189 (accept_3_5 2 112 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1
  112 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 111 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 111 189 3 26 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 111 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 111 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 189 3 25 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  73 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 189 3 24 37 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 111 189 3 23 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 111 189 (Polychromatic418967fa.accept_10_8_1_9_1_413
  68 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 67 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 189 3 22 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 65 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 189
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 64 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 111 189 3 21 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 189 (Polychromatic418967fa.accept_12_1_3_9_1_174
  61 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 189 3 20 37 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 189 3 19 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236
  56 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 189 3 18 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  52 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 189 3 17 37 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 189 3 16 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  47 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 189 3 15 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274 44 111 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 189 3 14 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 189
  (Polychromatic418967fa.accept_19_2_16_18_1_10922 40 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 111 189 3 13 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 189 3 12 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 111 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 189 3 11 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 189 3 10 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 189 (Polychromatic418967fa.accept_12_5_3_9_1_541
  29 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 189
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 189 3 9 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 111
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 189 3 8 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 189 3 7 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 189 (Polychromatic418967fa.accept_14_6_13_7_1_2015
  20 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 189 3 6 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 111
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 189 3 5 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 189 3 4 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 189 3 3 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 111 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 189 3 2 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 111 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 189 3 1 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 111 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 110
  189 (Eq.refl Bool.true) (allA_succ_of_accept 79 110 189 (accept_3_4 79 110 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 189 (accept_3_4 76 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 74 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 189 (accept_3_4 73 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 72 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 189 (accept_3_4 70 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 189 (Polychromatic418967fa.accept_25_18_10_14_1_10948 68 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 189 (accept_3_4 67 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 189 (accept_3_4 64 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 62 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 189 (accept_3_4 61 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 189 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 189 (accept_3_4 58 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 57 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 56 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 189 (accept_3_4 55 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 189 (accept_3_4 52 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 189 (Polychromatic418967fa.accept_17_16_8_2_1_5890 50 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 189 (accept_3_4 49 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 48 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 189 (accept_3_4 46 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 189 (accept_3_4 43 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 189 (accept_3_4 40 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 38 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 189 (accept_3_4 37 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 189 (Polychromatic418967fa.accept_20_16_10_9_1_9431 36 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 189 (accept_3_4 34 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 189 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 189 (Polychromatic418967fa.accept_24_8_14_21_1_10947 32 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 189 (accept_3_4 31 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 189 (accept_3_4 28 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 189 (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 189 (accept_3_4 25 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 189 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 189 (accept_3_4 22 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 189 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 189 (Polychromatic418967fa.accept_25_20_10_14_1_10910 20 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 189 (accept_3_4 19 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 189 (accept_3_4 16 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 189 (accept_3_4 13 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 110
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 189 (accept_3_4 10 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 189 (Polychromatic418967fa.accept_24_8_14_21_1_10947 8 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 189 (accept_3_4 7 110 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 110 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 189 (accept_3_4 4 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 110 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 189 (accept_3_4 1 110 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 109 189 (Eq.refl Bool.true) (allA_succ_of_accept 80 109 189 (accept_3_5 80 109 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 189 (Polychromatic418967fa.accept_19_3_14_18_1_6685 79 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 78 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 189 (accept_3_5 77 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 75 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 189 (accept_3_5 74 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 73 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 189
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 72 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 189 (accept_3_5 71 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 189 (Polychromatic418967fa.accept_28_13_25_21_1_10946 69 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 189 (accept_3_5 68 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 189
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 66 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 109 189 (accept_3_5 65 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 189 (accept_3_5 62 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 189
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 61 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 189 (Polychromatic418967fa.accept_14_4_11_7_1_1234 60 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 189 (accept_3_5 59 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 189
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 189 (accept_3_5 56 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 55 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 189 (accept_3_5 53 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 189 (accept_3_5 50 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 189 (Polychromatic418967fa.accept_17_15_7_2_1_2303 49 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 189 (Polychromatic418967fa.accept_19_10_14_18_1_10849 48 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 189 (accept_3_5 47 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 189 (accept_3_5 44 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 43 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 189 (Polychromatic418967fa.accept_15_12_4_9_1_3204 42 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 189 (accept_3_5 41 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 189 (accept_3_5 38 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 189 (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 189 (accept_3_5 35 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 109 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 189
  (Polychromatic418967fa.accept_23_10_17_5_1_5790 33 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 109 189 (accept_3_5 32 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 109 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 109 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 189 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 189 (accept_3_5 29 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 189
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 109 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 109 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 189 (accept_3_5 26 109 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 109 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 189 (accept_3_5 23 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 189 (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 189 (accept_3_5 20 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 189 (Polychromatic418967fa.accept_22_19_21_13_1_10945 19
  109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 189
  (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 189 (accept_3_5 17 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 189 (accept_3_5 14 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 109
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 189 (accept_3_5 11 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 189 (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 109 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 189 (accept_3_5 8 109 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 189 (Polychromatic418967fa.accept_19_7_14_18_1_6654 7 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 189
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 6 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 189 (accept_3_5 5 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 109 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 189 (accept_3_5 2 109 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 109 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 108 189 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 108 189 27 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 108 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 80 108 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 108 189
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 79 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 108 189 3 26 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 108 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 108 189 3 25 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 108 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 74 108 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 73
  108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 108 189 9 8 12 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 108 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 71 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 108 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 108 189 3 23 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 108 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711
  68 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 189
  (Polychromatic418967fa.accept_10_7_8_9_1_785 67 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 189 3 22 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 108 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 189 (Polychromatic418967fa.accept_10_4_8_9_1_784
  64 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 108 189 9 7 12 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 108 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 62 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 189 3 20 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 189 (Polychromatic418967fa.accept_11_4_9_2_1_259
  59 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 189
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 108 189 3 19 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 108 189 (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 108 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 189
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 189 27 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 189 (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 108 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 189
  (Polychromatic418967fa.accept_16_4_12_13_1_990 52 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 108 189 3 17 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 108 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 108 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 189 3 16 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 108 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 189
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 46 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 108 189 9 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 108 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 108
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 189 3 14 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 189 3 13 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520
  38 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 189
  (Polychromatic418967fa.accept_10_7_8_9_1_785 37 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 189 9 4 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 108
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 108 189 3 11 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 108 189
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 189 3 10 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 189 (Polychromatic418967fa.accept_11_7_9_2_1_260
  29 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 108 189 27 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 108 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 108 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 189 3 8 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 189
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 189 3 7 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 189 (Polychromatic418967fa.accept_15_5_3_9_1_283
  20 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 189
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 189 9 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 108
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 189 3 5 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 189 3 4 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 189 (Polychromatic418967fa.accept_10_1_8_9_1_787
  11 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 189
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 108 189 9 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 108 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 108 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 189 3 2 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 189
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 108 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 189 3 1 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 189 (Polychromatic418967fa.accept_30_2_18_9_1_10944 2 108
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 107
  189 (Eq.refl Bool.true) (allA_succ_of_accept 82 107 189 (accept_3_4 82 107 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 189 (Polychromatic418967fa.accept_28_25_23_21_1_4692 81 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 189 (accept_3_4 79 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 189 (Polychromatic418967fa.accept_19_1_12_18_1_10820 77 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 189 (accept_3_4 76 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 75 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 189 (accept_3_4 73 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 189 (accept_3_4 70 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 189 (accept_3_4 67 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 189 (Polychromatic418967fa.accept_17_14_5_2_1_4559 65 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 189 (accept_3_4 64 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 189 (accept_3_4 61 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 189 (Polychromatic418967fa.accept_23_13_15_5_1_4120 59 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 189 (accept_3_4 58 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 189 (Polychromatic418967fa.accept_20_17_7_9_1_8001 57 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 189 (accept_3_4 55 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710 53 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 189 (accept_3_4 52 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 189 (accept_3_4 49 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 189 (accept_3_4 46 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 189 (Polychromatic418967fa.accept_19_7_12_18_1_10848 45
  107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 189 (accept_3_4 43 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 189 (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 189 (accept_3_4 40 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 189 (accept_3_4 37 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 189 (accept_3_4 34 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 189 (accept_3_4 31 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 189 (Polychromatic418967fa.accept_22_7_19_13_1_10815 29 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 189 (accept_3_4 28 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 189 (accept_3_4 25 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 189 (accept_3_4 22 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 189 (accept_3_4 19 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 189 (accept_3_4 16 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 107
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 189 (accept_3_4 13 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 189 (accept_3_4 10 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 107 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 189 (accept_3_4 7 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 107 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 189 (accept_3_4 4 107 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 107 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 189 (accept_3_4 1 107 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 106 189 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 189 (accept_3_5 83 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 106 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 82 106 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 106 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 81 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 189 (accept_3_5 80 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 79 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 78 106 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 106 189 (accept_3_5 77 106 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 106 189 (Polychromatic418967fa.accept_14_6_8_7_1_589 76 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 106 189 (accept_3_5 74 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 106 189 (Polychromatic418967fa.accept_22_6_18_13_1_10907 72 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 106 189 (accept_3_5 71 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 106 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 106 189
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 69 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 106 189 (accept_3_5 68 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 66 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 106 189 (accept_3_5 65 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 106 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 106 189 (accept_3_5 62 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 106 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 106 189 (accept_3_5 59 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 106 189 (Polychromatic418967fa.accept_19_1_11_18_1_10841 58
  106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 189
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 106 189 (accept_3_5 56 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 106 189 (accept_3_5 53 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 106 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 52 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 106 189 (accept_3_5 50 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 106 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 106 189 (accept_3_5 47 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 106 189 (Polychromatic418967fa.accept_16_14_10_13_1_2768 46
  106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 106 189 (accept_3_5 44 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 106 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 106 189 (accept_3_5 41 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 106 189 (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 106 189 (accept_3_5 38 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 106 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 106 189 (accept_3_5 35 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 106 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 34 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 106 189 (accept_3_5 32 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 189 (accept_3_5 29 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 106 189 (Polychromatic418967fa.accept_16_12_10_13_1_1042 28
  106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 189 (accept_3_5 26 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 189 (Polychromatic418967fa.accept_22_2_18_13_1_10943 24 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 189 (accept_3_5 23 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 189
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 189 (accept_3_5 20 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 189 (accept_3_5 17 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 189 (Polychromatic418967fa.accept_22_16_18_13_1_5986 16
  106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 189 (accept_3_5 14 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 189 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 189 (accept_3_5 11 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 189 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 106
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 189 (accept_3_5 8 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 106 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 189 (accept_3_5 5 106 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 189 (Polychromatic418967fa.accept_19_4_11_18_1_3909 4 106 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 189 (accept_3_5 2 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 106 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 105 189 (Eq.refl Bool.true) (allA_succ_of_gcd 84 105 189 21 4 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 189
  (Polychromatic418967fa.accept_18_11_15_9_1_360 83 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 189 (Polychromatic418967fa.accept_17_14_3_2_1_5848 82 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 189 3 27 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 105 189 (Polychromatic418967fa.accept_26_2_1_7_1_10942
  80 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 189
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 79 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 189 3 26 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 105 189 7 11 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 105 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 105 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 189 3 25 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 74 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 189 3 24 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157
  71 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 189 7 10 15 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 105 189 3 23 35
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 68 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 189 (Polychromatic418967fa.accept_20_7_5_9_1_10833 67 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 189 3 22 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 105 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822
  65 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 189 21 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 105 189 (Polychromatic418967fa.accept_17_11_3_2_1_5867 62 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 105
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 189 3 20 35 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 58 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 189 3 19 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 105 189 7 8 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  55 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 189 3 18 35 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 189
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 53 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 189 3 17 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691
  50 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 105 189 7 7 15 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 105 189 3 16 35
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 46 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 189 3 15 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 44
  105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 189
  (Polychromatic418967fa.accept_19_5_10_18_1_2705 43 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 105 189 21 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 105 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 189
  (Polychromatic418967fa.accept_18_4_15_9_1_6882 40 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 189 3 13 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 189 (Polychromatic418967fa.accept_16_6_9_13_1_2751 38 105 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 189 3 12 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 105 189 7 5 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 105 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 34 105 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 189 3 11 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 189
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 189 3 10 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  29 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 105 189 7 4 15 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 105 189 3 9 35 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 189
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 189 (Polychromatic418967fa.accept_30_25_15_9_1_10941 25 105 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 189 3 8 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 189
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 23 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 189 (Polychromatic418967fa.accept_16_6_9_13_1_2751 22 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 189 21 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 105 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 189
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 189 3 6 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 105
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 189 3 5 35 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 189 7 2 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 189
  (Polychromatic418967fa.accept_25_13_5_14_1_10940 13 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 105 189 3 4 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 105 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 189
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 105 189 3 3 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 105 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 105 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 189 7 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 105 189 3 2 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845
  5 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 105 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 189 3 1 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 189 (Polychromatic418967fa.accept_19_2_10_18_1_6691 2 105 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 105 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 104 189
  (Eq.refl Bool.true) (allA_succ_of_accept 85 104 189 (accept_3_4 85 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 104 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 84 104 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 104 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 104 189 (accept_3_4 82 104 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 104 189
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 81 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 104 189 (Polychromatic418967fa.accept_15_5_14_9_1_274 80 104 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 189 (accept_3_4 79 104 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 189 (accept_3_4 76 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 74 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 189 (accept_3_4 73 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 72 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 189 (accept_3_4 70 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 69 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 189 (accept_3_4 67 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 189 (accept_3_4 64 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 189 (Polychromatic418967fa.accept_19_5_9_18_1_10839 62 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 189 (accept_3_4 61 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 60 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 189 (accept_3_4 58 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 189 (Polychromatic418967fa.accept_14_1_6_7_1_1936 57 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 189 (Polychromatic418967fa.accept_23_10_12_5_1_10857 56 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 189 (accept_3_4 55 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 189 (accept_3_4 52 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 51 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 50 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 189 (accept_3_4 49 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 189 (accept_3_4 46 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 189 (accept_3_4 43 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 189 (accept_3_4 40 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 189 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 189 (accept_3_4 37 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 189 (accept_3_4 34 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 189 (Polychromatic418967fa.accept_19_13_9_18_1_10939 32 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 189 (accept_3_4 31 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 189 (accept_3_4 28 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 189 (Polychromatic418967fa.accept_25_1_4_14_1_10893 26 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 189 (accept_3_4 25 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 189 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 189 (accept_3_4 22 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 189 (Polychromatic418967fa.accept_15_5_14_9_1_274 20 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 189 (accept_3_4 19 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 189 (accept_3_4 16 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 189 (Polychromatic418967fa.accept_20_14_4_9_1_2249 14 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 189 (accept_3_4 13 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 104
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 189 (accept_3_4 10 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 189 (Polychromatic418967fa.accept_22_9_16_13_1_10938 9 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 104 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 189 (accept_3_4 7 104 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 189 (accept_3_4 4 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 104 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 189 (Polychromatic418967fa.accept_19_2_9_18_1_6651 2 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 189 (accept_3_4 1 104 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 104
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 103 189
  (Eq.refl Bool.true) (allA_succ_of_accept 86 103 189 (accept_3_5 86 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 103 189 (Polychromatic418967fa.accept_19_9_8_18_1_1571 85 103 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 103
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 189 (accept_3_5 83 103
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 189
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 81 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 189 (accept_3_5 80 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 79 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 189 (accept_3_5 77 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 75 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 189 (accept_3_5 74 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 189 (accept_3_5 71 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 189
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 189 (accept_3_5 68 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 67 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 189 (accept_3_5 65 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 189 (accept_3_5 62 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 189 (accept_3_5 59 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 189
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 57 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 189 (accept_3_5 56 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 189 (Polychromatic418967fa.accept_20_15_3_9_1_5007 55 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 189 (accept_3_5 53 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 189 (accept_3_5 50 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 48 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 189 (accept_3_5 47 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 189 (accept_3_5 44 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 189 (accept_3_5 41 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 189 (accept_3_5 38 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 189 (accept_3_5 35 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 189
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 189 (accept_3_5 32 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 189 (accept_3_5 29 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 189 (accept_3_5 26 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 189 (Polychromatic418967fa.accept_16_9_7_13_1_4997 25 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 189 (accept_3_5 23 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 189
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 189 (accept_3_5 20 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 189 (accept_3_5 17 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 189 (accept_3_5 14 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 189 (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 189 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 189 (accept_3_5 11 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 189 (accept_3_5 8 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 189 (accept_3_5 5 103 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 189 (accept_3_5 2 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 189 (Polychromatic418967fa.accept_19_1_8_18_1_6667 1 103 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 88 102 189 (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 189 3 29 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 102 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 85 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 189 3 28 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 82 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 102 189 3 27 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 80 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 79 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 189 3 26 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 77 102 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 189 (Polychromatic418967fa.accept_12_4_6_9_1_548
  76 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 102 189 3 25 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 102 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 74 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 189 (Polychromatic418967fa.accept_14_3_4_7_1_175 73 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 102 189 3 24 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 102 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 102 189 3 23 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 189 3 22 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 65 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 64 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 102 189 3 21 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 102 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 102 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 189 (Polychromatic418967fa.accept_10_1_2_9_1_152
  61 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 189 3 20 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 102 189 3 19 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 102 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  56 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 189 3 18 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 53 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 102 189 3 17 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 102 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 102 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 189 (Polychromatic418967fa.accept_15_4_12_9_1_773
  49 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 189 3 16 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 102 189 3 15 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 189 3 14 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 41 102 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 189 (Polychromatic418967fa.accept_12_4_6_9_1_548
  40 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 189 3 13 34 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 102 189 3 12 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 102 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 102 189 3 11 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 189 3 10 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 102 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 102 189 3 9 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 102 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 102
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 189 3 8 34 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 189 3 7 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 189 3 6 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 102
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 189 3 5 34 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 189 (Polychromatic418967fa.accept_20_13_2_9_1_4958 13 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 189 3 4 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 189 3 3 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 189 3 2 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 5 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 102 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 189 3 1 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 102 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 102 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 101 189 (Eq.refl Bool.true) (allA_succ_of_accept 88 101 189 (accept_3_4 88 101 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 87 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 189 (accept_3_4 85 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 189 (Polychromatic418967fa.accept_18_12_11_9_1_4257 84 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 189 (Polychromatic418967fa.accept_19_7_6_18_1_8123 83 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 189 (accept_3_4 82 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 81 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 189 (accept_3_4 79 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 77 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 189 (accept_3_4 76 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 189 (accept_3_4 73 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 189 (Polychromatic418967fa.accept_24_23_5_21_1_5462 71 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 189 (accept_3_4 70 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 69 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 189 (accept_3_4 67 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 189 (Polychromatic418967fa.accept_14_10_3_7_1_1975 66 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 65 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 189 (accept_3_4 64 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 189 (accept_3_4 61 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 189 (Polychromatic418967fa.accept_17_8_16_2_1_10847 59 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 189 (accept_3_4 58 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 57 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 189 (accept_3_4 55 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 189 (Polychromatic418967fa.accept_24_6_5_21_1_10892 54 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 189 (accept_3_4 52 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 189 (accept_3_4 49 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 47 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 189 (accept_3_4 46 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 189 (accept_3_4 43 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 189 (accept_3_4 40 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 189 (accept_3_4 37 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 189 (accept_3_4 34 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 189 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 189 (accept_3_4 31 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 189 (accept_3_4 28 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 189 (accept_3_4 25 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 189 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 189 (Polychromatic418967fa.accept_24_23_5_21_1_5462 23 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 189 (accept_3_4 22 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 189 (accept_3_4 19 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 189 (accept_3_4 16 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 189 (accept_3_4 13 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 189 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 189 (accept_3_4 10 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 101
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 189 (accept_3_4 7 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 101 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 189 (accept_3_4 4 101 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 101 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 189 (accept_3_4 1 101 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 100 189
  (Eq.refl Bool.true) (allA_succ_of_accept 89 100 189 (accept_3_5 89 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 100 189 (Polychromatic418967fa.accept_16_8_4_13_1_1014 88 100 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 87 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 189 (accept_3_5 86 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 85 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 100 189 (Polychromatic418967fa.accept_13_6_9_7_1_2430 84 100 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 100 189 (accept_3_5 83 100 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 100 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 82 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 81 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 100 189 (accept_3_5 80 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 78 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 189 (accept_3_5 77 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 100 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 100 189
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 75 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 100 189 (accept_3_5 74 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 100 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 72 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 100 189 (accept_3_5 71 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 100 189 (Polychromatic418967fa.accept_16_6_4_13_1_3841 70 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 100 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 100 189 (accept_3_5 68 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 66 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 100 189 (accept_3_5 65 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 100 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 64 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 189
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 100 189 (accept_3_5 62 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 100 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 100 189 (accept_3_5 59 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 100 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 57 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 100 189 (accept_3_5 56 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 100 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 189 (accept_3_5 53 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 189 (Polychromatic418967fa.accept_28_24_16_21_1_10937 52
  100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 189
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 51 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 189 (accept_3_5 50 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 189 (Polychromatic418967fa.accept_15_3_10_9_1_769 48 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 189 (accept_3_5 47 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 189 (Polychromatic418967fa.accept_15_1_10_9_1_1495 46 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 189 (accept_3_5 44 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 189 (accept_3_5 41 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 189
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 189 (accept_3_5 38 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 189 (accept_3_5 35 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 189 (accept_3_5 32 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 189 (accept_3_5 29 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 27 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 189 (accept_3_5 26 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 189 (accept_3_5 23 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 189 (Polychromatic418967fa.accept_16_6_4_13_1_3841 22 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 189 (accept_3_5 20 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 189 (accept_3_5 17 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 189
  (Polychromatic418967fa.accept_13_2_9_7_1_164 15 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 189 (accept_3_5 14 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 189 (accept_3_5 11 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 100
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 189 (accept_3_5 8 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 100 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 189 (accept_3_5 5 100 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 100 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 189 (accept_3_5 2 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_189_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


