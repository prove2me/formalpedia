-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch194
-- name    : Polychromatic418967fa_Branch194
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:19.603114+00:00
-- url     : https://prove2.me/theorems/f283b037-081a-4399-a468-64b640b81211
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch194_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_194 : allB 194 194 :=
  allB_succ' 2 193 194 (Eq.refl Bool.true) (allA_of_3_0 2 193 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  192 194 (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 194 2 1 96 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 194 (accept_3_2 1 192 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192 194))) (allB_succ' 4 191 194 (Eq.refl Bool.true) (allA_succ_of_accept 3 191 194
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 191 194 (Polychromatic418967fa.accept_18_2_11_14_1_69 2 191 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 194 (accept_3_2 1 191 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 191 194)))) (allB_succ' 5 190 194 (Eq.refl Bool.true) (allA_of_3_0 5 190 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 189 194 (Eq.refl Bool.true) (allA_succ_of_accept 5 189 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 194 (accept_3_2 4 189 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 194 (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 189 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 194 (accept_3_2 1 189 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 194)))))) (allB_succ' 7 188 194 (Eq.refl Bool.true) (allA_succ_of_gcd 6
  188 194 2 3 94 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  5 188 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 188 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 194 2 2 94 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 188 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 194 2 1 94 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 194 (accept_3_2 1 188 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 194))))))) (allB_succ' 8 187 194 (Eq.refl Bool.true) (allA_of_3_0 8 187 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 186 194 (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 194 2 4 93
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 194
  (accept_3_2 7 186 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 194 2 3 93 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 194
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 186 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 194 2 2 93 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 186 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 186 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 194 2 1 93 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 194 (accept_3_2 1 186 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 186 194))))))))) (allB_succ' 10 185 194 (Eq.refl Bool.true) (allA_succ_of_accept 9 185 194
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 185 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 194 (accept_3_2 7 185 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 194 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 185 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 194 (Polychromatic418967fa.accept_11_5_9_7_1_411 5
  185 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 194 (accept_3_2 4 185
  194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 194 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 185 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 194
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 185 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 194 (accept_3_2 1 185 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  194)))))))))) (allB_succ' 11 184 194 (Eq.refl Bool.true) (allA_of_3_0 11 184 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 183 194 (Eq.refl Bool.true) (allA_succ_of_accept 11 183 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 194 (accept_3_2 10 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 183 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 194 (accept_3_2 7 183 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 194 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 183 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 194 (accept_3_2 4 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 183 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 183 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 194 (accept_3_2 1 183 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 194)))))))))))) (allB_succ' 13 182 194 (Eq.refl Bool.true) (allA_succ_of_gcd 12 182
  194 2 6 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  182 194 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 182 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 182 194 2 5 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 182 194 (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 182 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 182 194 2 4 91 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 182 194 (accept_3_2 7 182 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182 194 2 3 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 182 194 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 182 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 194 2 2 91 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 194
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 182 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 182 194 2 1 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 182 194 (accept_3_2 1 182 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  194))))))))))))) (allB_succ' 14 181 194 (Eq.refl Bool.true) (allA_of_3_0 14 181 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 180 194 (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 194 2 7 90 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 194 (accept_3_2 13 180 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 194 2 6 90 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 194
  (Polychromatic418967fa.accept_21_11_12_5_1_2224 11 180 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 180 194 2 5 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 180 194 (Polychromatic418967fa.accept_21_9_12_5_1_317 9 180 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 194 2 4 90 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 194 (accept_3_2 7 180 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 194 2 3 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 194 (Polychromatic418967fa.accept_19_5_9_4_1_232 5 180 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 194 2 2 90 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 194
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 180 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 194 2 1 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 194 (accept_3_2 1 180 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  194))))))))))))))) (allB_succ' 16 179 194 (Eq.refl Bool.true) (allA_succ_of_accept 15 179 194
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 179 194 (Polychromatic418967fa.accept_19_14_8_4_1_2961 14 179 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 194 (accept_3_2 13 179 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 179 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 179 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 194 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 194 (accept_3_2 10
  179 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 179 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 179 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 194 (accept_3_2 7 179 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 179 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 179 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 194 (accept_3_2 4 179
  194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 194 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 194
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 194 (accept_3_2 1 179 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  194)))))))))))))))) (allB_succ' 17 178 194 (Eq.refl Bool.true) (allA_of_3_0 17 178 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 177 194 (Eq.refl Bool.true) (allA_succ_of_accept 17 177 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 194 (accept_3_2 16 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 194 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 177 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 194 (accept_3_2 13 177 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 177 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 194 (accept_3_2 10 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 194 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 177 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 194 (accept_3_2 7 177 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 194 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 177 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 194 (accept_3_2 4 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 194 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 177 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 194 (accept_3_2 1 177 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 194)))))))))))))))))) (allB_succ' 19 176 194 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 176 194 2 9 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 176 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 194 2 8 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 194 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  176 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 194 2 7 88 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 194 (accept_3_2 13
  176 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 194 2 6 88 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 194
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 176 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 194 2 5 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 176 194 (Polychromatic418967fa.accept_19_9_5_4_1_1866 9 176 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 194 2 4 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 194 (accept_3_2 7 176 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 176 194 2 3 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 176 194 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 176 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 194 2 2 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 3
  176 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 194 2 1 88 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 194 (accept_3_2 1
  176 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 194))))))))))))))))))) (allB_succ' 20 175 194 (Eq.refl
  Bool.true) (allA_of_3_0 20 175 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 174 194 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 174 194 2 10 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 194 (accept_3_2 19 174 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 194 2 9 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 174 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 194 2 8 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 194 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  174 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 194 2 7 87 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 194 (accept_3_2 13
  174 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 194 2 6 87 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 194
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 174 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 194 2 5 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 174 194 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 174 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 194 2 4 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 194 (accept_3_2 7 174 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 174 194 2 3 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 174 194 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 174 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 194 2 2 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 174 194 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  174 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 194 2 1 87 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 194 (accept_3_2 1
  174 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 194))))))))))))))))))))) (allB_succ' 22 173 194
  (Eq.refl Bool.true) (allA_succ_of_accept 21 173 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 194
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 194 (accept_3_2 19 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 194 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 173 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 194 (accept_3_2 16 173 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 194
  (Polychromatic418967fa.accept_19_14_2_4_1_8473 14 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 194 (accept_3_2 13 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 194 (accept_3_2 10 173 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 194
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 194 (accept_3_2 7 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 194 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 194 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 173 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 194 (accept_3_2 4 173 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 194
  (Polychromatic418967fa.accept_13_2_4_12_1_745 2 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 194 (accept_3_2 1 173 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  194)))))))))))))))))))))) (allB_succ' 23 172 194 (Eq.refl Bool.true) (allA_of_3_0 23 172 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 171 194 (Eq.refl Bool.true) (allA_succ_of_accept 23 171 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 194 (accept_3_2 22 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 194 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 171 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 194 (accept_3_2 19 171 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 171
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 194 (accept_3_2 16 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 194 (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 171 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 194 (accept_3_2 13 171 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 194 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 171
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 194 (accept_3_2 10 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 171 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 194 (accept_3_2 7 171 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 171 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 194 (accept_3_2 4 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 194 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 171 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 171 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 194 (accept_3_2 1 171 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 194)))))))))))))))))))))))) (allB_succ' 25 170 194 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 170 194 2 12 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 194 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 170 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 194 2 11 85 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 194
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 170 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 194 2 10 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 194 (accept_3_2 19 170 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 194 2 9 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 170 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 170 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 194 2 8 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  170 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 170 194 2 7 85 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 194 (accept_3_2 13
  170 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 194 2 6 85 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 194
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 170 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 194 2 5 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 170 194 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 170 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 194 2 4 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 194 (accept_3_2 7 170 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 170 194 2 3 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 170 194 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 170 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 170 194 2 2 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  170 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 194 2 1 85 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 194 (accept_3_2 1
  170 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 194))))))))))))))))))))))))) (allB_succ' 26 169 194
  (Eq.refl Bool.true) (allA_of_3_0 26 169 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 168 194 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 168 194 2 13 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 168 194 (accept_3_2 25 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 194 2 12 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 194 (Polychromatic418967fa.accept_20_3_8_14_1_5342 23 168 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 194 2 11 84 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 194
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 194 2 10 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 194 (accept_3_2 19 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 194 2 9 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 194 2 8 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 194 (Polychromatic418967fa.accept_11_4_3_7_1_828
  15 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 194 2 7 84 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 194
  (accept_3_2 13 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 194 2 6 84 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 194
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 194 2 5 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 168 194 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 168 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 194 2 4 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 194 (accept_3_2 7 168 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 168 194 2 3 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 168 194 (Polychromatic418967fa.accept_17_5_15_7_1_4992 5 168 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 194 2 2 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 168 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 3
  168 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 194 2 1 84 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 194 (accept_3_2 1
  168 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 194))))))))))))))))))))))))))) (allB_succ' 28 167 194
  (Eq.refl Bool.true) (allA_succ_of_accept 27 167 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 194
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 194 (accept_3_2 25 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 194 (Polychromatic418967fa.accept_19_5_15_4_1_4224 24 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 194 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 167 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 194 (accept_3_2 22 167 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 194
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 194 (accept_3_2 19 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 194 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 194 (accept_3_2 16 167 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 194
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 167 194 (accept_3_2 13 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 167 194 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 167 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 194 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 167 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 194 (accept_3_2 10 167 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 194
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 194 (accept_3_2 7 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 194 (Polychromatic418967fa.accept_14_6_13_12_1_810 6 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 194 (accept_3_2 4 167 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 194
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 194 (accept_3_2 1 167 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  194)))))))))))))))))))))))))))) (allB_succ' 29 166 194 (Eq.refl Bool.true) (allA_of_3_0 29 166 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 165 194 (Eq.refl Bool.true) (allA_succ_of_accept 29 165 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 194 (accept_3_2 28 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 194 (accept_3_2 25 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 165 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 194 (accept_3_2 22 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 194 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 194 (accept_3_2 19 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 194 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 165 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 194 (accept_3_2 16 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 194 (Polychromatic418967fa.accept_19_14_13_4_1_11247 14 165 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 194 (accept_3_2 13 165 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 194 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 165
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 194 (accept_3_2 10 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 194 (accept_3_2 7 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 165 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 194 (accept_3_2 4 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 194 (accept_3_2 1 165 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 194)))))))))))))))))))))))))))))) (allB_succ' 31 164 194 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 164 194 2 15 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 164 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 194 2 14 82 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 194
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 164 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 194 2 13 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 194 (accept_3_2 25 164 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 194 2 12 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 164 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 194 2 11 82 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 194
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 164 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 194 2 10 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 194 (accept_3_2 19 164 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 194 2 9 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 164 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 194 2 8 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  164 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 194 2 7 82 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 194 (accept_3_2 13
  164 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 194 2 6 82 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 194
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 164 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 194 2 5 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 164 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 164 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 194 2 4 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 194 (accept_3_2 7 164 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 164 194 2 3 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 164 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 164 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 194 2 2 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  164 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 194 2 1 82 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 194 (accept_3_2 1
  164 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 194))))))))))))))))))))))))))))))) (allB_succ' 32 163
  194 (Eq.refl Bool.true) (allA_of_3_0 32 163 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 162 194
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 194 2 16 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 194 (accept_3_2 31 162 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 194 2 15 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 194 (Polychromatic418967fa.accept_21_8_15_5_1_8178 29 162 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 194 2 14 81 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 194
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 194 2 13 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 194 (accept_3_2 25 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 194 2 12 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 194 (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 162 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 194 2 11 81 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 194
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 194 2 10 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 194 (accept_3_2 19 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 194 2 9 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 162 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 194 2 8 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 194 (Polychromatic418967fa.accept_11_4_8_7_1_819
  15 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 194 2 7 81 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 194
  (accept_3_2 13 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 194 2 6 81 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 194
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 162 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 194 2 5 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 162 194 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 162 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 194 2 4 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 194 (accept_3_2 7 162 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 162 194 2 3 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 162 194 (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 162 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 194 2 2 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 162 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 3
  162 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 194 2 1 81 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 194 (accept_3_2 1
  162 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 194))))))))))))))))))))))))))))))))) (allB_succ' 34 161
  194 (Eq.refl Bool.true) (allA_succ_of_accept 33 161 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 194
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 194 (accept_3_2 31 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 194 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 194 (accept_3_2 28 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 194
  (Polychromatic418967fa.accept_20_6_1_14_1_11258 26 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 161 194 (accept_3_2 25 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 161 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 194 (accept_3_2 22 161 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 194
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 194 (accept_3_2 19 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 194 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 194 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 194 (accept_3_2 16 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 194
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 194 (accept_3_2 13 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 194 (accept_3_2 10 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 194
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 194 (accept_3_2 7 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 194 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 194 (accept_3_2 4 161 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 194
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 194 (accept_3_2 1 161 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  194)))))))))))))))))))))))))))))))))) (allB_succ' 35 160 194 (Eq.refl Bool.true) (allA_of_3_0 35 160 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 159 194 (Eq.refl Bool.true) (allA_succ_of_accept 35 159 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 194 (accept_3_2 34 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 194 (Polychromatic418967fa.accept_19_13_7_4_1_1869 32 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 194 (accept_3_2 31 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 159 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 194 (accept_3_2 28 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 194 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 194 (accept_3_2 25 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 194 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 159 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 194 (accept_3_2 22 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 194 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 194 (accept_3_2 19 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 194 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 194 (accept_3_2 16 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 194 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 194 (Polychromatic418967fa.accept_17_14_6_7_1_4980 14 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 194 (accept_3_2 13 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 194 (accept_3_2 10 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 194 (accept_3_2 7 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 159 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 194 (accept_3_2 4 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 159 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 194 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 194 (accept_3_2 1 159 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 194)))))))))))))))))))))))))))))))))))) (allB_succ' 37 158 194 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 158 194 2 18 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 194 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 158 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 194 2 17 79 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 194
  (Polychromatic418967fa.accept_21_12_11_5_1_6549 33 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 158 194 2 16 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 158 194 (accept_3_2 31 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 194 2 15 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 158 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 194 2 14 79 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 194
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 194 2 13 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 194 (accept_3_2 25 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 194 2 12 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 158 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 194 2 11 79 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 194
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 194 2 10 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 194 (accept_3_2 19 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 194 2 9 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 194 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 158 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 194 2 8 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 194 2 7 79 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 194 (accept_3_2 13
  158 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 194 2 6 79 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 194
  (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 194 2 5 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 158 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 194 2 4 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 194 (accept_3_2 7 158 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 194 2 3 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 194 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 158 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 194 2 2 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 194 (Polychromatic418967fa.accept_11_3_4_7_1_114 3
  158 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 194 2 1 79 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 194 (accept_3_2 1
  158 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 194))))))))))))))))))))))))))))))))))))) (allB_succ' 38
  157 194 (Eq.refl Bool.true) (allA_of_3_0 38 157 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 156 194
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 194 2 19 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 194 (accept_3_2 37 156 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 156 194 2 18 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 156 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 156 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 194 2 17 78 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 194
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 194 2 16 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 194 (accept_3_2 31 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 194 2 15 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 156 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 194 2 14 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 194
  (Polychromatic418967fa.accept_17_10_3_7_1_1679 27 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 194 2 13 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 194 (accept_3_2 25 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 194 2 12 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 194 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 156 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 194 2 11 78 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 194
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 194 2 10 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 194 (accept_3_2 19 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 194 2 9 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 156 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 194 2 8 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 194 2 7 78 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 194 (accept_3_2 13
  156 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 194 2 6 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 194
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 194 2 5 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 194 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 156 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 194 2 4 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 194 (accept_3_2 7 156 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 156 194 2 3 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 156 194 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 156 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 194 2 2 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  156 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 194 2 1 78 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 194 (accept_3_2 1
  156 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 194))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 155 194 (Eq.refl Bool.true) (allA_succ_of_accept 39 155 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 194
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 194 (accept_3_2 37 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 194 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 194 (accept_3_2 34 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 194
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 194 (accept_3_2 31 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 194 (accept_3_2 28 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 194
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 194 (accept_3_2 25 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 194 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 194 (accept_3_2 22 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 194
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 194 (accept_3_2 19 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 194 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 194 (accept_3_2 16 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 194
  (Polychromatic418967fa.accept_21_14_8_5_1_6586 14 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 194 (accept_3_2 13 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 194 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 194 (accept_3_2 10 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 194
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 194 (accept_3_2 7 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 194 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 194 (accept_3_2 4 155 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 194
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 194 (accept_3_2 1 155 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  194)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 154 194 (Eq.refl Bool.true) (allA_of_3_0 41 154 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 153 194 (Eq.refl Bool.true) (allA_succ_of_accept 41 153 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 194 (accept_3_2 40 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 194 (Polychromatic418967fa.accept_16_6_9_2_1_6518 38 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 194 (accept_3_2 37 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 194 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 153 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 194 (accept_3_2 34 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 194 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 194 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 153 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 194 (accept_3_2 31 153 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 194 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 194 (accept_3_2 28 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 194 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 194 (accept_3_2 25 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 194 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24
  153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 194 (accept_3_2 22 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 194 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 194 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 194 (accept_3_2 19 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 194 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 153 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 194 (accept_3_2 16 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 194 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 194 (accept_3_2 13 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 194 (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 153
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 194 (accept_3_2 10 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 194 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 194 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 153 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 194 (accept_3_2 7 153 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 194 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 194 (accept_3_2 4 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 194 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 194 (accept_3_2 1 153 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 194)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 152 194
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 152 194 2 21 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 152 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 194 2 20 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 194
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 194 2 19 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 194 (accept_3_2 37 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 194 2 18 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 194 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 152 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 194 2 17 76 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 194
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 194 2 16 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 194 (accept_3_2 31 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 194 2 15 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 194 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 152 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 194 2 14 76 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 194
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 194 2 13 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 194 (accept_3_2 25 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 194 2 12 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 194 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 152 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 194 2 11 76 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 194
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 194 2 10 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 194 (accept_3_2 19 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 194 2 9 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 194 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 152 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 194 2 8 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 194 2 7 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 194 (accept_3_2 13
  152 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 194 2 6 76 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 194
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 194 2 5 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 194 (Polychromatic418967fa.accept_22_9_20_18_1_8035 9 152 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 194 2 4 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 194 (accept_3_2 7 152 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 194 2 3 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 194 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 152 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 194 2 2 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  152 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 194 2 1 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 194 (accept_3_2 1
  152 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 194)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 151 194 (Eq.refl Bool.true) (allA_of_3_0 44 151 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 150 194 (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 194 2 22 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 194 (accept_3_2 43 150 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 194 2 21 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 194 (Polychromatic418967fa.accept_16_9_6_2_1_3101
  41 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 194 2 20 75 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 194
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 194 2 19 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 194 (accept_3_2 37 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 194 2 18 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 150 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 194 2 17 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 194
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 194 2 16 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 194 (accept_3_2 31 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 194 2 15 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 150 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 194 2 14 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 194
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 194 2 13 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 194 (accept_3_2 25 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 194 2 12 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 150 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 194 2 11 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 194
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 194 2 10 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 194 (accept_3_2 19 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 194 2 9 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 194 2 8 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 194 2 7 75 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 194 (accept_3_2 13
  150 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 194 2 6 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 194
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 194 2 5 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 150 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 150 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 194 2 4 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 194 (accept_3_2 7 150 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 150 194 2 3 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 150 194 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 150 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 194 2 2 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 3
  150 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 194 2 1 75 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 194 (accept_3_2 1
  150 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 194)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 149 194 (Eq.refl Bool.true) (allA_succ_of_accept 45 149 194 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 194
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 194 (accept_3_2 43 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 194 (Polychromatic418967fa.accept_22_20_17_18_1_11276 42 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 194 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 149 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 194 (accept_3_2 40 149 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 194
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 194 (accept_3_2 37 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 194 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 194 (accept_3_2 34 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 194
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 194 (accept_3_2 31 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 194 (Polychromatic418967fa.accept_19_11_16_4_1_7075 30 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 194 (Polychromatic418967fa.accept_16_13_5_2_1_2131 29 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 194 (accept_3_2 28 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 194
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 194 (accept_3_2 25 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 194 (accept_3_2 22 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 194
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 194 (accept_3_2 19 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 194 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 194 (accept_3_2 16 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 194
  (Polychromatic418967fa.accept_28_14_9_26_1_11275 14 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 149 194 (accept_3_2 13 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 194 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 149 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 194 (accept_3_2 10 149 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 194
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 194 (accept_3_2 7 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 194 (Polychromatic418967fa.accept_17_6_13_7_1_272 6 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 194 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 194 (accept_3_2 4 149 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 194
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 194 (accept_3_2 1 149 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  194)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 148 194 (Eq.refl Bool.true) (allA_of_3_0 47 148 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 147 194 (Eq.refl Bool.true) (allA_succ_of_accept 47 147 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 194 (accept_3_2 46 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 194 (accept_3_2 43 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 194 (accept_3_2 40 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 194 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 194 (accept_3_2 37 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 194 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 194 (accept_3_2 34 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 194 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 194 (accept_3_2 31 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 194 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 147
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 194 (accept_3_2 28 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 194 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 194 (accept_3_2 25 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 194 (accept_3_2 22 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 194 (accept_3_2 19 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 194 (accept_3_2 16 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 194 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 194 (accept_3_2 13 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 194 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 194 (accept_3_2 10 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 194 (accept_3_2 7 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 194
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 194 (accept_3_2 4 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 194 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 194 (accept_3_2 1 147 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 194)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 146 194 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 146 194 2 24 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 146 194 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 146 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 194 2 23 73 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 194
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 194 2 22 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 194 (accept_3_2 43 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 194 2 21 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 194 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 146 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 194 2 20 73 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 194
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 194 2 19 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 194 (accept_3_2 37 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 194 2 18 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 146 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 194 2 17 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 194
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 194 2 16 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 194 (accept_3_2 31 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 194 2 15 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 194 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 146 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 194 2 14 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 194
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 146 194 2 13 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 146 194 (accept_3_2 25 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 194 2 12 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 194 (Polychromatic418967fa.accept_21_2_20_5_1_6599 23 146 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 194 2 11 73 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 194
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 194 2 10 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 194 (accept_3_2 19 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 194 2 9 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 146 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 194 2 8 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 194 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 194 2 7 73 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 194 (accept_3_2 13
  146 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 194 2 6 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 194
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 194 2 5 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 194 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 146 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 194 2 4 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 194 (accept_3_2 7 146 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 194 2 3 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 194 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 146 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 194 2 2 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  146 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 194 2 1 73 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 194 (accept_3_2 1
  146 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 194)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 145 194 (Eq.refl Bool.true) (allA_of_3_0 50 145 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 144 194 (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 194 2 25 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 194 (accept_3_2 49 144 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 194 2 24 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 194 (Polychromatic418967fa.accept_13_8_1_12_1_762
  47 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 194 2 23 72 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 194
  (Polychromatic418967fa.accept_19_7_11_4_1_1872 45 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 194 2 22 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 194 (accept_3_2 43 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 194 2 21 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 144 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 194 2 20 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 194
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 194 2 19 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 194 (accept_3_2 37 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 194 2 18 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 194 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 144 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 194 2 17 72 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 194
  (Polychromatic418967fa.accept_17_16_8_7_1_4983 33 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 194 2 16 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 194 (accept_3_2 31 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 194 2 15 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 144 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 194 2 14 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 194
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 194 2 13 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 194 (accept_3_2 25 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 194 2 12 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 144 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 194 2 11 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 194
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 194 2 10 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 194 (accept_3_2 19 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 194 2 9 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 194 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 144 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 194 2 8 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 194 2 7 72 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 194 (accept_3_2 13
  144 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 194 2 6 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 194
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 194 2 5 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 194 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 194 2 4 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 194 (accept_3_2 7 144 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 194 2 3 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 144 194 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 144 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 194 2 2 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 194 (Polychromatic418967fa.accept_19_3_11_4_1_8466
  3 144 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 194 2 1 72 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 194 (accept_3_2 1
  144 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 194)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 143 194 (Eq.refl Bool.true) (allA_succ_of_accept 51 143 194 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 194
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 194 (accept_3_2 49 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 194 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 194 (accept_3_2 46 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 194
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 194 (accept_3_2 43 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 194 (accept_3_2 40 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 194
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 194 (accept_3_2 37 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 194 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 194 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 194 (accept_3_2 34 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 194
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 194 (accept_3_2 31 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 194 (accept_3_2 28 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 194
  (Polychromatic418967fa.accept_22_4_11_18_1_1892 26 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 143 194 (accept_3_2 25 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 194 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 194 (accept_3_2 22 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 194
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 194 (accept_3_2 19 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 194 (Polychromatic418967fa.accept_23_18_5_10_1_11274 18 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 194 (accept_3_2 16 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 194
  (Polychromatic418967fa.accept_19_14_10_4_1_11240 14 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 143 194 (accept_3_2 13 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 143 194 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 194 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 194 (accept_3_2 10 143 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 194
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 194 (accept_3_2 7 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 194 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 194 (accept_3_2 4 143 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 194
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 194 (accept_3_2 1 143 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  194)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 142 194 (Eq.refl Bool.true) (allA_of_3_0 53 142
  194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 141 194 (Eq.refl Bool.true) (allA_succ_of_accept 53 141
  194 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 194 (accept_3_2 52 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 194 (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 194 (accept_3_2 49 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 194 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 141 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 194 (accept_3_2 46 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 194 (accept_3_2 43 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 194 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 194 (accept_3_2 40 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 194 (accept_3_2 37 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 194 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 141 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 194 (accept_3_2 34 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 194 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 194 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 194 (accept_3_2 31 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 194 (accept_3_2 28 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 194 (accept_3_2 25 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 194 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 194 (accept_3_2 22 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 194 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 194 (accept_3_2 19 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 194 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 194 (accept_3_2 16 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 194 (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 194 (accept_3_2 13 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 194 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 141 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 194
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 194 (accept_3_2 10 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 194 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 194 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 194 (accept_3_2 7 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 194 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 194
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 194 (accept_3_2 4 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 194 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 194 (accept_3_2 1 141 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 194)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 140 194
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 140 194 2 27 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 140 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 194 2 26 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 194
  (Polychromatic418967fa.accept_15_6_5_14_1_429 51 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 194 2 25 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 194 (accept_3_2 49 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 194 2 24 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 194 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 140 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 194 2 23 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 194
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 194 2 22 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 194 (accept_3_2 43 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 194 2 21 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 194 2 20 70 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 194
  (Polychromatic418967fa.accept_15_9_5_14_1_973 39 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 194 2 19 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 194 (accept_3_2 37 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 194 2 18 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 194 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 140 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 194 2 17 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 194
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 140 194 2 16 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 140 194 (accept_3_2 31 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 194 2 15 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 140 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 194 2 14 70 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 194
  (Polychromatic418967fa.accept_31_27_16_8_1_4392 27 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 194 2 13 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 140 194 (accept_3_2 25 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 194 2 12 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 194 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 194 2 11 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 194
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 140 194 2 10 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 140 194 (accept_3_2 19 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 194 2 9 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 194 2 8 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 194 (Polychromatic418967fa.accept_11_4_8_7_1_819
  15 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 194 2 7 70 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 194
  (accept_3_2 13 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 194 2 6 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 194
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 194 2 5 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 194 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 140 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 194 2 4 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 194 (accept_3_2 7 140 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 194 2 3 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 194 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 194 2 2 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 194 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3
  140 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 194 2 1 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 194 (accept_3_2 1
  140 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  194))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 139 194 (Eq.refl Bool.true) (allA_of_3_0 56
  139 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 138 194 (Eq.refl Bool.true) (allA_succ_of_gcd 56 138
  194 2 28 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  138 194 (accept_3_2 55 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 138 194 2 27 69 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 138 194
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 194 2 26 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 138 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 194 2 25 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 194 (accept_3_2 49 138 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 194 2 24 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 47
  138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 194 2 23 69 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 194
  (Polychromatic418967fa.accept_11_1_6_7_1_116 45 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 194 2 22 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 194 (accept_3_2 43 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 194 2 21 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 194 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 138 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 194 2 20 69 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 194
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 194 2 19 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 194 (accept_3_2 37 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 194 2 18 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 194 2 17 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 194
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 194 2 16 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 194 (accept_3_2 31 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 194 2 15 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 194 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 138 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 194 2 14 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 194
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 194 2 13 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 194 (accept_3_2 25 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 194 2 12 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 194 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 138 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 194 2 11 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 194
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 194 2 10 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 194 (accept_3_2 19 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 194 2 9 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 194 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 194 2 8 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 194 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 194 2 7 69 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 194 (accept_3_2 13
  138 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 194 2 6 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 194
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 194 2 5 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 194 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 138 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 194 2 4 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 194 (accept_3_2 7 138 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 194 2 3 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 194 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 138 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 194 2 2 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 194 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  138 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 194 2 1 69 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 194 (accept_3_2 1
  138 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  194))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 137 194 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 137 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 194 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 194 (accept_3_2 55 137
  194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 194
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 137 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 194 (accept_3_2 52 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 194 (accept_3_2 49
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 194
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 194 (accept_3_2 46 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 137 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 194 (Polychromatic418967fa.accept_7_2_4_5_1_313
  44 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 194 (accept_3_2 43
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 194
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 137 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 194 (accept_3_2 40 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 194 (Polychromatic418967fa.accept_16_6_9_2_1_6518
  38 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 194 (accept_3_2 37
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 194
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 194 (accept_3_2 34 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 137 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 194 (Polychromatic418967fa.accept_10_2_7_4_1_967
  32 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 194 (accept_3_2 31
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 194
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 137 194 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 194 (accept_3_2 28 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 194 (Polychromatic418967fa.accept_9_8_2_5_1_237
  26 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 194 (accept_3_2 25
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 194
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 194 (accept_3_2 22 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 137 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 194 (Polychromatic418967fa.accept_7_6_4_5_1_314
  20 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 194 (accept_3_2 19
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 194
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 137 194 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 194 (accept_3_2 16 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 194
  (Polychromatic418967fa.accept_21_14_11_5_1_6591 14 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 137 194 (accept_3_2 13 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 137 194 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 137 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 194 (accept_3_2 10 137 194
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 194 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 194
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 194 (accept_3_2 7 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 194 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 194 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 137 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 194 (accept_3_2 4 137 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 194 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 194
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 194
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 194 (accept_3_2 1 137 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  194)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 136 194 (Eq.refl Bool.true) (allA_of_3_0
  59 136 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 135 194 (Eq.refl Bool.true) (allA_succ_of_accept 59
  135 194 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 135 194 (accept_3_2 58 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 194 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 135
  194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 194 (accept_3_2 55 135
  194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 194
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 194 (accept_3_2 52 135 194 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 194 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 194
  (Polychromatic418967fa.accept_19_12_2_4_1_9882 50 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 194 (accept_3_2 49 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 194 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 194 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 194 (accept_3_2 46 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 194
  (Polychromatic418967fa.accept_16_12_7_2_1_4159 44 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 194 (accept_3_2 43 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 194 (accept_3_2 40 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 194 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 194
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 194 (accept_3_2 37 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 194 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 194 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 194 (accept_3_2 34 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 194
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 194 (accept_3_2 31 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 194 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 194 (accept_3_2 28 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 194 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 194
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 194 (accept_3_2 25 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 194 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 194 (accept_3_2 22 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 194
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 194 (accept_3_2 19 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 194 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 194 (accept_3_2 16 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 194 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 194
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 194 (accept_3_2 13 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 194 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 194 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 194 (accept_3_2 10 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 194
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 194 (accept_3_2 7 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 194 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 194 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 194 (accept_3_2 4 135 194 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 194 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 194 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 194
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 194 (accept_3_2 1 135 194 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  194))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_194_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


