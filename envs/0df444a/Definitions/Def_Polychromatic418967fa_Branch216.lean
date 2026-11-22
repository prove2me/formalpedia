-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch216
-- name    : Polychromatic418967fa_Branch216
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:25:05.165152+00:00
-- url     : https://prove2.me/theorems/2c67a6bd-c218-4702-9209-d779d3ed70f5
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch216_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_216 : allB 216 216 :=
  allB_succ' 2 215 216 (Eq.refl Bool.true) (allA_succ_of_accept 1 215 216 (accept_3_4 1 215 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 216)) (allB_succ' 3 214 216 (Eq.refl Bool.true) (allA_succ_of_gcd 2 214 216 2 1 107
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 216
  (Polychromatic418967fa.accept_13_1_6_8_1_208 1 214 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 216))) (allB_succ' 4 213 216 (Eq.refl Bool.true) (allA_succ_of_gcd 3 213 216 3 1 71 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 213 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 213 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 216)))) (allB_succ' 5 212 216 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  212 216 4 1 53 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 212 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 212 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 212 216 2 1 106 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 212 216 (accept_3_4 1 212 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 212 216))))) (allB_succ' 6 211 216 (Eq.refl Bool.true) (allA_succ_of_accept 5 211 216 (accept_3_5 5 211 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 216 (Polychromatic418967fa.accept_16_4_3_8_1_2486
  4 211 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 211 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 216 (accept_3_5 2 211 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 216 (Polychromatic418967fa.accept_19_1_2_7_1_2054 1 211 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 216)))))) (allB_succ' 7 210 216 (Eq.refl Bool.true) (allA_succ_of_gcd 6 210 216 6 1 35 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 216
  (Polychromatic418967fa.accept_20_5_10_16_1_9890 5 210 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 216 2 2 105 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 210 216 3 1 70 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 210 216 2 1 105 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 210 216 (Polychromatic418967fa.accept_17_1_6_12_1_1944 1 210 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 216))))))) (allB_succ' 8 209 216 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 209 216 (accept_3_4 7 209 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 209 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 209 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 216 (accept_3_4 4 209 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 209 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 216
  (Polychromatic418967fa.accept_21_2_20_6_1_2277 2 209 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 216 (accept_3_4 1 209 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  216)))))))) (allB_succ' 9 208 216 (Eq.refl Bool.true) (allA_succ_of_gcd 8 208 216 8 1 26 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 216
  (Polychromatic418967fa.accept_15_7_13_6_1_696 7 208 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 208 216 2 3 104 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 208 216 (accept_3_5 5 208 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 208 216 4 1 52 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 208 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 208 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 216 2 1 104 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1
  208 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 216))))))))) (allB_succ' 10 207 216
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 207 216 9 1 23 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 207 216 (Polychromatic418967fa.accept_17_8_3_12_1_5354 8 207 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 216
  (Polychromatic418967fa.accept_13_7_12_8_1_199 7 207 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 207 216 3 2 69 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 207 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 207 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 216 3 1 69 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 207 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 207 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 216)))))))))) (allB_succ' 11 206 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 206 216 2 5 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 206 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 206 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 206 216 2 4 103 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 206 216 (accept_3_4 7 206 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 206 216 2 3 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 206 216 (Polychromatic418967fa.accept_15_5_11_6_1_692 5
  206 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 216 2 2 103 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 216
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 206 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 216 2 1 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 216 (accept_3_4 1 206 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  216))))))))))) (allB_succ' 12 205 216 (Eq.refl Bool.true) (allA_succ_of_accept 11 205 216 (accept_3_5 11 205 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 10
  205 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 216 (accept_3_5 8 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 216 (Polychromatic418967fa.accept_17_6_1_12_1_4115 6 205 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 216 (accept_3_5 5 205 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 205 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 216 (accept_3_5 2 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 216)))))))))))) (allB_succ' 13 204 216 (Eq.refl Bool.true) (allA_succ_of_gcd 12 204 216 12 1
  17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 216
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 204 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 216 2 5 102 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 204 216 3 3 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 204 216 4 2 51 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 204 216 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 204 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 216 6 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5
  204 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 216 4 1 51 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 216 3 1 68 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 216 2 1 102 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 216
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 204 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 216))))))))))))) (allB_succ' 14 203 216 (Eq.refl Bool.true) (allA_succ_of_accept 13 203 216 (accept_3_4
  13 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 216
  (Polychromatic418967fa.accept_16_12_11_8_1_832 12 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 203 216 (Polychromatic418967fa.accept_17_11_16_12_1_1984 11 203 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 216 (accept_3_4 10 203 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 203 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 216 (accept_3_4 7 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 216 (Polychromatic418967fa.accept_19_6_13_7_1_4464 6 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 216 (Polychromatic418967fa.accept_16_5_11_8_1_3431 5 203 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 216 (accept_3_4 4 203 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 216 (Polychromatic418967fa.accept_16_3_11_8_1_830 3 203 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 216
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 216 (accept_3_4 1 203 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  216)))))))))))))) (allB_succ' 15 202 216 (Eq.refl Bool.true) (allA_succ_of_gcd 14 202 216 2 7 101 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 216
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 202 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 216 2 6 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 216 (accept_3_5 11 202 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 216 2 5 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 202 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 216 2 4 101 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 216
  (Polychromatic418967fa.accept_21_7_13_6_1_349 7 202 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 216 2 3 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 216 (accept_3_5 5 202 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 216 2 2 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 202 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 216 2 1 101 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 202 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 216))))))))))))))) (allB_succ' 16 201 216 (Eq.refl Bool.true) (allA_succ_of_gcd 15 201 216 3 5 67 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 216
  (Polychromatic418967fa.accept_13_1_6_8_1_208 14 201 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 201 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 216 3 4 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  201 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 216
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 201 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 201 216 3 3 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 201 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 201 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 201 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 216 3 2 67 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 201 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 201 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 216 3 1 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 201 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 201 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 216)))))))))))))))) (allB_succ' 17 200 216 (Eq.refl Bool.true) (allA_succ_of_gcd 16 200 216 8 2 25 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 216
  (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 200 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 200 216 2 7 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 200 216 (accept_3_4 13 200 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 216 4 3 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 200 216 (Polychromatic418967fa.accept_15_11_5_6_1_669 11 200 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 216 2 5 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  200 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 216 8 1 25 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 216 (accept_3_4 7
  200 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 216 2 3 100 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 200 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 200 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 200 216 4 1 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 200 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 200 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 216 2 1 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 216 (accept_3_4 1 200 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 200 216))))))))))))))))) (allB_succ' 18 199 216 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 199 216 (accept_3_5 17 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 199 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 216 (accept_3_5 14 199 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 199 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 216
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 216 (accept_3_5 11 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 216 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 199 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 216 (accept_3_5 8 199 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 216 (Polychromatic418967fa.accept_22_7_1_18_1_12756 7 199 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 216 (accept_3_5 5 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 199 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 199 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 216 (accept_3_5 2 199 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 216 (Polychromatic418967fa.accept_16_1_7_8_1_3422 1 199 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 216)))))))))))))))))) (allB_succ' 19 198 216
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 198 216 18 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 198 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 198 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 216 2 8 99 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 216 3 5 66 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 216 2 7 99 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 198 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 216 6 2 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 198 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 198 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 216 2 5 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 216 9 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 216 2 4 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7
  198 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 216 6 1 33 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 216
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 198 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 216 2 2 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 198 216 3 1 66 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 198 216 2 1 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 198 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 198 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 216))))))))))))))))))) (allB_succ' 20 197 216 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 197 216 (accept_3_4 19 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 216 (Polychromatic418967fa.accept_25_18_22_16_1_12851 18 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 216 (Polychromatic418967fa.accept_22_17_21_18_1_12850 17 197 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 216 (accept_3_4 16 197 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 216
  (Polychromatic418967fa.accept_21_15_8_6_1_5106 15 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 197 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 216 (accept_3_4 13 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 197 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 197 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 216 (Polychromatic418967fa.accept_10_1_7_6_1_91
  11 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 216 (accept_3_4 10
  197 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 197 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 216 (accept_3_4 7 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 197 216 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 197 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5
  197 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 216 (accept_3_4 4 197
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 197 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 197 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 216 (accept_3_4 1 197 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 197 216)))))))))))))))))))) (allB_succ' 21 196 216 (Eq.refl Bool.true) (allA_succ_of_gcd 20 196
  216 4 5 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  196 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 196 216 2 9 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 196 216 (accept_3_5 17 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 216 4 4 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 196 216 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 196 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 216 2 7 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 216 (Polychromatic418967fa.accept_11_2_9_7_1_124
  13 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 216 4 3 49 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 216
  (accept_3_5 11 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 216 2 5 98 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 216
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 196 216 4 2 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 196 216 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 196 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 216 2 3 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 216 (accept_3_5 5 196 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 216 4 1 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 196 216 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 196 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 216 2 1 98 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 216
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 196 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 216))))))))))))))))))))) (allB_succ' 22 195 216 (Eq.refl Bool.true) (allA_succ_of_gcd 21 195 216 3 7 65
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 195 216
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 195 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 216 3 6 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 216 (Polychromatic418967fa.accept_19_17_5_7_1_5896
  17 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 216
  (Polychromatic418967fa.accept_28_16_27_20_1_12849 16 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 195 216 3 5 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 195 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 195 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 216
  (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 195 216 3 4 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 195 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 195 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 216 (Polychromatic418967fa.accept_17_10_8_12_1_6559 10 195
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 216 3 3 65 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 216
  (Polychromatic418967fa.accept_22_8_19_18_1_12714 8 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 195 216 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 195 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 216 3 2 65 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 216
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 195 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 216 3 1 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 216 (Polychromatic418967fa.accept_19_2_5_7_1_10021 2 195 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 195 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 195 216)))))))))))))))))))))) (allB_succ' 23 194 216 (Eq.refl Bool.true) (allA_succ_of_gcd 22 194 216 2 11
  97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 216
  (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 216 2 10 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 216 (accept_3_4 19 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 216 2 9 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 194 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 216 2 8 97 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 216 2 7 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 216 (accept_3_4 13 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 216 2 6 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 194 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 216 2 5 97 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 216
  (Polychromatic418967fa.accept_13_9_12_8_1_570 9 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 216 2 4 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 216 (accept_3_4 7 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  216 2 3 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 194 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 216 2 2 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 216 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 194 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 216 2 1 97 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 216 (accept_3_4 1 194 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 216))))))))))))))))))))))) (allB_succ' 24 193 216 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 193 216 (accept_3_5 23 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 193 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 193 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 216 (Polychromatic418967fa.accept_22_21_17_18_1_12848 21
  193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 216 (accept_3_5 20
  193 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 193 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 193 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 216 (accept_3_5 17 193 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 193 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 193 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 216
  (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 216 (accept_3_5 14 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 216 (Polychromatic418967fa.accept_19_13_3_7_1_4423 13 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 193 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 216 (accept_3_5 11 193 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 193 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 216 (accept_3_5 8 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 193 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 216 (accept_3_5 5 193 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 193
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 216 (accept_3_5 2 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 193 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 216)))))))))))))))))))))))) (allB_succ' 25 192 216 (Eq.refl Bool.true) (allA_succ_of_gcd 24
  192 216 24 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 192 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 192 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 192 216 2 11 96 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 216 3 7 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 216 4 5 48 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 216 (Polychromatic418967fa.accept_21_19_3_6_1_2281 19 192 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 216 6 3 32 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 216
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 192 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 216 8 2 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 192 216 3 5 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 192 216 2 7 96 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 216 (Polychromatic418967fa.accept_19_13_2_7_1_8738 13 192 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 216 12 1 16 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 192 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 216 2 5 96 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 192 216 3 3 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 192 216 8 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 192 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 192 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 216 6 1 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127
  5 192 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 216 4 1 48 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 216 3 1 64 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 216 2 1 96 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 192 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 216))))))))))))))))))))))))) (allB_succ' 26 191 216 (Eq.refl Bool.true) (allA_succ_of_accept 25 191 216
  (accept_3_4 25 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 191 216 (Polychromatic418967fa.accept_16_7_15_8_1_278 23 191 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 216 (accept_3_4 22 191 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 191 216 (Polychromatic418967fa.accept_19_2_1_7_1_8683 21 191 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 216 (accept_3_4 19 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 216 (accept_3_4 16 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 191 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 216
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 216 (accept_3_4 13 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 216 (accept_3_4 10 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 191 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 216 (accept_3_4 7 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 216 (Polychromatic418967fa.accept_19_6_1_7_1_5872 6 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 216 (accept_3_4 4 191 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 191 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 216 (accept_3_4 1 191 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  216)))))))))))))))))))))))))) (allB_succ' 27 190 216 (Eq.refl Bool.true) (allA_succ_of_gcd 26 190 216 2 13 95 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 216
  (Polychromatic418967fa.accept_17_8_3_12_1_5354 25 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 216 2 12 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 216 (accept_3_5 23 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 216 2 11 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 190 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 216 2 10 95 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 216 2 9 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 216 (accept_3_5 17 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 216 2 8 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 216 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 190 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 216 2 7 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 216
  (Polychromatic418967fa.accept_22_13_14_18_1_3237 13 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 190 216 2 6 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 190 216 (accept_3_5 11 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 216 2 5 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 190 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 216 2 4 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 216
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 216 2 3 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 216 (accept_3_5 5 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  216 2 2 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 190 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 216 2 1 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 190 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 216))))))))))))))))))))))))))) (allB_succ' 28 189
  216 (Eq.refl Bool.true) (allA_succ_of_gcd 27 189 216 27 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 189 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 189
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 25 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 189 216 3 8 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 189 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 189 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 189
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 216 3 7 63 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 216
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 189 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 216 9 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 216
  (Polychromatic418967fa.accept_19_17_18_7_1_11434 17 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 189 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 189 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 216 3 5 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 189 216
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 189 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 216 3 4 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  11 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 216
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 189 216 9 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 189 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 189 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 216 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 189
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 216 3 2 63 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 189 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 216 3 1 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 189 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 216
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 189 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 216)))))))))))))))))))))))))))) (allB_succ' 29 188 216 (Eq.refl Bool.true) (allA_succ_of_gcd 28 188 216
  4 7 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188
  216 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 188 216 2 13 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 188 216 (accept_3_4 25 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 216 4 6 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 188 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 188 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 216 2 11 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 216 (Polychromatic418967fa.accept_16_5_12_8_1_2521
  21 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 216 4 5 47 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 216
  (accept_3_4 19 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 216 2 9 94 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 216
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 188 216 4 4 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 188 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 188 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 216 2 7 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 216 (accept_3_4 13 188 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 216 4 3 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 216 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 188
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 216 2 5 94 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 216
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 216 4 2 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 216 (accept_3_4 7 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  216 2 3 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 216 (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 188 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 216 4 1 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 188 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 216 2 1 94 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 216 (accept_3_4 1 188 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 188 216))))))))))))))))))))))))))))) (allB_succ' 30 187 216 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 187 216 (accept_3_5 29 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 187 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 187 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 187
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 216 (accept_3_5 26 187
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 187 216 (Polychromatic418967fa.accept_21_3_19_6_1_5081 24 187 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 216 (accept_3_5 23 187 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 187 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 187 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 216 (Polychromatic418967fa.accept_10_1_7_6_1_91
  21 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 216 (accept_3_5 20
  187 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 216
  (Polychromatic418967fa.accept_16_3_11_8_1_830 19 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 187 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 187 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 216 (accept_3_5 17 187 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 187 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 187 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 216 (accept_3_5 14 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 216 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 187 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 216 (accept_3_5 11 187 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 187
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 216
  (Polychromatic418967fa.accept_19_9_16_7_1_1056 9 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 216 (accept_3_5 8 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 216 (Polychromatic418967fa.accept_22_7_11_18_1_12847 7 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 216 (Polychromatic418967fa.accept_19_6_16_7_1_11433 6 187 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 216 (accept_3_5 5 187 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 187 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 216 (accept_3_5 2 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 187 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 216)))))))))))))))))))))))))))))) (allB_succ' 31 186 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 186 216 6 5 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 216 (Polychromatic418967fa.accept_26_3_4_8_1_11024 29 186 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 216 2 14 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 186 216 3 9 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 186 216 2 13 93 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 186 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 216 6 4 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 186 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 186 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 216 2 11 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 216 3 7 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 216 2 10 93 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 186 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 216 6 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 186 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 216 2 8 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 216 3 5 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 216 2 7 93 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 216
  (Polychromatic418967fa.accept_17_13_16_12_1_6562 13 186 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 186 216 6 2 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 186 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 186 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 216 2 5 93 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 216 3 3 62 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 216 2 4 93 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 216
  (Polychromatic418967fa.accept_20_7_6_16_1_11369 7 186 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 216 6 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 186 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 216 2 2 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 216 3 1 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 216 2 1 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 216 (Polychromatic418967fa.accept_17_1_16_12_1_5298
  1 186 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  216))))))))))))))))))))))))))))))) (allB_succ' 32 185 216 (Eq.refl Bool.true) (allA_succ_of_accept 31 185 216
  (accept_3_4 31 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 185 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 185 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 216 (accept_3_4 28 185 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 185 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 216
  (Polychromatic418967fa.accept_15_11_5_6_1_669 26 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 216 (accept_3_4 25 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 216 (accept_3_4 22 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 216
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 216 (accept_3_4 19 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 216 (Polychromatic418967fa.accept_16_1_9_8_1_2438 17 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 216 (accept_3_4 16 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 216 (Polychromatic418967fa.accept_16_15_9_8_1_2440 15 185
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 216
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 216 (accept_3_4 13 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 216 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 216 (accept_3_4 10 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 216
  (Polychromatic418967fa.accept_19_8_14_7_1_10047 8 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 216 (accept_3_4 7 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 216 (Polychromatic418967fa.accept_19_6_14_7_1_5902 6 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 216 (accept_3_4 4 185 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 216 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 185 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 216 (accept_3_4 1 185 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  216)))))))))))))))))))))))))))))))) (allB_succ' 33 184 216 (Eq.refl Bool.true) (allA_succ_of_gcd 32 184 216 8 4 23 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 216 2 15 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 216 (accept_3_5 29 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 216 4 7 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 184 216 (Polychromatic418967fa.accept_28_27_16_20_1_12846 27 184 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 216 2 13 92 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 216 8 3 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 184 216 (accept_3_5 23 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  184 216 2 11 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 184 216 (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 184 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 216 4 5 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 216 (Polychromatic418967fa.accept_13_6_2_8_1_1782
  19 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 216 2 9 92 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 216
  (accept_3_5 17 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 216 8 2 23 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 184 216 2 7 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 184 216 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 184 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 216 4 3 46 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 216 (accept_3_5 11 184 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 216 2 5 92 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 216
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 216 8 1 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 184 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 216 2 3 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 216 (accept_3_5 5 184 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 216 4 1 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 184 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 184 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 216 2 1 92 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 184 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 216))))))))))))))))))))))))))))))))) (allB_succ' 34 183 216 (Eq.refl Bool.true) (allA_succ_of_gcd 33 183
  216 3 11 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  183 216 (Polychromatic418967fa.accept_13_6_1_8_1_1116 32 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 183 216 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 183 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 216 3 10 61 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 216
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 183 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 183 216 3 9 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 183 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 26
  183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 216
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 183 216 3 8 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 183 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 183 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742 22 183
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 216 3 7 61 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 216
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 183 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 216 3 6 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 216 (Polychromatic418967fa.accept_10_7_3_6_1_644
  17 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 216 3 5 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 216 (Polychromatic418967fa.accept_19_14_12_7_1_10027 14 183 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 216
  (Polychromatic418967fa.accept_20_13_3_16_1_4020 13 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 183 216 3 4 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 183 216 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 183 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 216
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 216 3 3 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 183 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 183 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 216 3 2 61 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 216 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 183 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 216 3 1 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 183 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 216
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 183 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 216)))))))))))))))))))))))))))))))))) (allB_succ' 35 182 216 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  182 216 2 17 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 182 216 (Polychromatic418967fa.accept_19_14_11_7_1_7236 33 182 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 216 2 16 91 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 216 (accept_3_4 31 182 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 216 2 15 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 216 (Polychromatic418967fa.accept_21_8_14_6_1_9800
  29 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 216 2 14 91 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 216
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 216 2 13 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 216 (accept_3_4 25 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 216 2 12 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 182 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 216 2 11 91 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 216 2 10 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 216 (accept_3_4 19 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 216 2 9 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 216 (Polychromatic418967fa.accept_25_17_7_16_1_12845 17 182 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 216 2 8 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 216
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 15 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 216 2 7 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 216 (accept_3_4 13 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 216 2 6 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 182 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 216 2 5 91 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 216
  (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 216 2 4 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 216 (accept_3_4 7 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  216 2 3 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 216 (Polychromatic418967fa.accept_28_5_14_20_1_12844 5 182 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 216 2 2 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 216 (Polychromatic418967fa.accept_21_3_14_6_1_11325 3 182 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 216 2 1 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 216 (accept_3_4 1 182 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 216))))))))))))))))))))))))))))))))))) (allB_succ' 36 181 216
  (Eq.refl Bool.true) (allA_succ_of_accept 35 181 216 (accept_3_5 35 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 181 216 (Polychromatic418967fa.accept_22_12_5_18_1_12843 34 181 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 216 (Polychromatic418967fa.accept_13_7_12_8_1_199
  33 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 216 (accept_3_5 32
  181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 31 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 181 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 30 181 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 216 (accept_3_5 29 181 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 181 216 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 216 (accept_3_5 26 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 216 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 216 (accept_3_5 23 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 181
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 216
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 216 (accept_3_5 20 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 216 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 216 (accept_3_5 17 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 216 (Polychromatic418967fa.accept_17_16_11_12_1_2008 16
  181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 216
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 216 (accept_3_5 14 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 216 (Polychromatic418967fa.accept_16_13_5_8_1_5814 13 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 216 (accept_3_5 11 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 216 (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 181
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 216 (accept_3_5 8 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 216 (Polychromatic418967fa.accept_17_6_11_12_1_4107 6 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 216 (accept_3_5 5 181 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 181 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 216
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 216 (accept_3_5 2 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 181 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 216)))))))))))))))))))))))))))))))))))) (allB_succ' 37 180 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 180 216 36 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 180 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 216 2 17 90 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 216 3 11 60 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 216 4 8 45 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 216
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 31 180 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 216 6 5 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 180 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 216 4 7 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 216 9 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 216 2 13 90 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 180 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 216 12 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 180 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 216 2 11 90 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 216 3 7 60 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 216 4 5 45 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 216
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 180 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 216 18 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 180 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 216 4 4 45 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 216 3 5 60 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 216 2 7 90 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 216
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 180 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 216 12 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 180 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 216 2 5 90 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 216 9 1 20 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 216 4 2 45 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 216
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 180 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 216 6 1 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 216 (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 180 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 216 4 1 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 216 3 1 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 216 2 1 90 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 180 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 216)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 179 216 (Eq.refl Bool.true) (allA_succ_of_accept 37 179 216 (accept_3_4 37 179 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 216 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 216 (accept_3_4 34 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 216 (accept_3_4 31 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 179 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 216
  (Polychromatic418967fa.accept_16_13_3_8_1_2422 29 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 216 (accept_3_4 28 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 216 (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 179 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 216 (accept_3_4 25 179 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 216 (accept_3_4 22 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 216 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 216 (accept_3_4 19 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 179
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 216 (accept_3_4 16 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 216 (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 216 (accept_3_4 13 179 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 216
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 216 (accept_3_4 10 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 179 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 216 (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 179
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 216 (accept_3_4 7 179 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 216 (Polychromatic418967fa.accept_19_6_8_7_1_10023
  6 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 216 (accept_3_4 4 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 179 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 179 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 216 (accept_3_4 1 179 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 216)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 178 216 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 178 216 2 19 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 178 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 178 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 178 216 2 18 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 178 216 (accept_3_5 35 178 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 178 216 2 17 89 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 178 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 178 216 2 16 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 178 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 178 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 178 216 2 15 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 178 216 (accept_3_5 29 178 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 178 216 2 14 89 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 178 216
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 178 216 2 13 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 178 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 178 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 178 216 2 12 89 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 178 216 (accept_3_5 23 178 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 178 216 2 11 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 178 216 (Polychromatic418967fa.accept_17_4_8_12_1_9165
  21 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 216 2 10 89 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 216
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 216 2 9 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 216 (accept_3_5 17 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 216 2 8 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 216 (Polychromatic418967fa.accept_20_15_18_16_1_5441 15 178 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 216 2 7 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 216 2 6 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 216 (accept_3_5 11 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 216 2 5 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 178 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 216 2 4 89 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 216 2 3 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 216 (accept_3_5 5 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  216 2 2 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 178 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 216 2 1 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 216 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 178 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 216)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 177 216 (Eq.refl Bool.true) (allA_succ_of_gcd 39 177 216 3 13 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 177 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 216 3 12 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 216 (Polychromatic418967fa.accept_15_5_12_6_1_639
  35 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 216
  (Polychromatic418967fa.accept_21_13_9_6_1_1190 34 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 216 3 11 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 177 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31
  177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 177 216 3 10 59 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 216 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 216 3 9 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 216
  (Polychromatic418967fa.accept_20_6_17_16_1_8470 26 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 177 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 177 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 216 3 8 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 216
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 216 3 7 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 216 (Polychromatic418967fa.accept_15_5_12_6_1_639
  20 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 216
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 19 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 177 216 3 6 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 177 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 216 (Polychromatic418967fa.accept_19_16_6_7_1_4425 16 177
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 216 3 5 59 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 216
  (Polychromatic418967fa.accept_19_14_6_7_1_7223 14 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 216 3 4 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 216 3 3 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 216 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 177
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 216 3 2 59 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 216
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 216 3 1 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 177 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 177 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 216)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 176 216 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 176 216 8 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 176 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 176 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 176 216 2 19 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 176 216 (accept_3_4 37 176 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 176 216 4 9 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 216 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 176
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 216 2 17 88 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 216 8 4 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 176 216 (accept_3_4 31 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  176 216 2 15 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 176 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 176 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 216 4 7 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  27 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 216 2 13 88 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 216
  (accept_3_4 25 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 216 8 3 22 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 176 216 2 11 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 176 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 176 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 216 4 5 44 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 216 (accept_3_4 19 176 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 216 2 9 88 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 216
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 176 216 8 2 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 176 216 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 176 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 216 2 7 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 216 (accept_3_4 13 176 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 216 4 3 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 216 (Polychromatic418967fa.accept_17_11_6_12_1_5348 11 176
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 216 2 5 88 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 216 8 1 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 216 (accept_3_4 7 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  216 2 3 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 176 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 216 4 1 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 176 216 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 176 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 216 2 1 88 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 216 (accept_3_4 1 176 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 176 216))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 175 216
  (Eq.refl Bool.true) (allA_succ_of_accept 41 175 216 (accept_3_5 41 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 175 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 175 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 216 (accept_3_5 38 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 216
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 37 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 175 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 175 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 216 (accept_3_5 35 175 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 175 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 216
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 216 (accept_3_5 32 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 216 (Polychromatic418967fa.accept_19_11_4_7_1_1029 30 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 216 (accept_3_5 29 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 216 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 216
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 216 (accept_3_5 26 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 216 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 216 (accept_3_5 23 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 216 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 21 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 216 (accept_3_5 20 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 216 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 18 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 216 (accept_3_5 17 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 216
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 216 (accept_3_5 14 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 216 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 216 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 216 (accept_3_5 11 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 216 (Polychromatic418967fa.accept_17_10_5_12_1_4101 10 175
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 216 (accept_3_5 8 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 216 (Polychromatic418967fa.accept_16_7_15_8_1_278 7 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 216 (Polychromatic418967fa.accept_23_6_14_9_1_12750 6 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 216 (accept_3_5 5 175 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 216 (accept_3_5 2 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 175 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 216)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 174 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 174 216 6 7 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 174 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 216 2 20 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 216 3 13 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 216 2 19 87 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 216
  (Polychromatic418967fa.accept_25_12_24_16_1_12842 37 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 174 216 6 6 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 174 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 174 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 216 2 17 87 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 216 3 11 58 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 216 2 16 87 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 216
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 216 6 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 174 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 174 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 216 2 14 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 216 3 9 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 216 2 13 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 216 6 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 174 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 216 2 11 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 216 3 7 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 216 2 10 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 216
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 216 6 3 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 216 (Polychromatic418967fa.accept_22_17_20_18_1_1899 17 174 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 216 2 8 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 216 3 5 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 216 2 7 87 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 216
  (Polychromatic418967fa.accept_11_2_9_7_1_124 13 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 216 6 2 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 174 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 216 2 5 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 216 3 3 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 216 2 4 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 216 (Polychromatic418967fa.accept_17_7_4_12_1_4084
  7 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 216 6 1 29 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 216
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 174 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 216 2 2 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 174 216 3 1 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 174 216 2 1 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 174 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 174 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 216))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 173 216
  (Eq.refl Bool.true) (allA_succ_of_accept 43 173 216 (accept_3_4 43 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 173 216 (Polychromatic418967fa.accept_17_8_3_12_1_5354 42 173 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747 41 173
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 216 (accept_3_4 40 173
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 173 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 173 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 216 (accept_3_4 37 173 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 173 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 216 (Polychromatic418967fa.accept_13_9_4_8_1_1752
  35 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 216 (accept_3_4 34
  173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 216
  (Polychromatic418967fa.accept_19_14_2_7_1_12841 33 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 216 (accept_3_4 31 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 216 (Polychromatic418967fa.accept_22_8_19_18_1_12714 30 173 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 216 (accept_3_4 28 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 216 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 216 (accept_3_4 25 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 173
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 216
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 216 (accept_3_4 22 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 216 (Polychromatic418967fa.accept_16_5_13_8_1_2454 21 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 216 (Polychromatic418967fa.accept_16_4_13_8_1_3424 20 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 216 (accept_3_4 19 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 173 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 216
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 216 (accept_3_4 16 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 216 (accept_3_4 13 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 216 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 173
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 216 (accept_3_4 10 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 216 (accept_3_4 7 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 216 (Polychromatic418967fa.accept_28_6_5_20_1_12840 6 173 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 216
  (Polychromatic418967fa.accept_16_5_13_8_1_2454 5 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 216 (accept_3_4 4 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 216 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 173 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 216 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 216 (accept_3_4 1 173 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 216)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 172 216 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 172 216 4 11 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 172 216 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 172 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 172 216 2 21 86 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 172 216 (accept_3_5 41 172 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 172 216 4 10 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 172 216
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 172 216 2 19 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 172 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 172 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 172 216 4 9 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 172 216 (accept_3_5 35 172 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 172 216 2 17 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 172 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 216 4 8 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 216 2 15 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 216 (accept_3_5 29 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 216 4 7 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 172 216 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 172 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 216 2 13 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 216 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  25 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 216 4 6 43 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 216
  (accept_3_5 23 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 216 2 11 86 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 216 4 5 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 172 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 216 2 9 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 216 (accept_3_5 17 172 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 216 4 4 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 216 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 172
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 216 2 7 86 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 216
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 216 4 3 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 172 216 (accept_3_5 11 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  172 216 2 5 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 172 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 216 4 2 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 216 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 172 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 216 2 3 86 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 216 (accept_3_5 5
  172 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 216 4 1 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 216 2 1 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172 216))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 171 216
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 171 216 9 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 171 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 171 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 216
  (Polychromatic418967fa.accept_21_1_3_6_1_8321 43 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 171 216 3 14 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 171 216 (Polychromatic418967fa.accept_20_1_11_16_1_699 41 171 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 216
  (Polychromatic418967fa.accept_17_6_1_12_1_4115 40 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 216 3 13 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 171 216 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 171 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 171 216 9 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 171 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 171
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 216 3 11 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 216 (Polychromatic418967fa.accept_25_6_21_16_1_12839 31 171 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 216 3 10 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 216
  (Polychromatic418967fa.accept_16_13_11_8_1_2449 29 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 171 216 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 171 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 216 9 3 19 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 216
  (Polychromatic418967fa.accept_20_6_11_16_1_3992 26 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 171 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 171 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 216 3 8 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 216 3 7 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 216 (Polychromatic418967fa.accept_13_7_2_8_1_1746
  20 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 216
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 171 216 9 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 216 3 5 57 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 216
  (Polychromatic418967fa.accept_21_14_3_6_1_8231 14 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 216 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 171 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 216 3 4 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 216 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 216 9 1 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 216 (Polychromatic418967fa.accept_21_8_3_6_1_11279 8 171 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 216
  (Polychromatic418967fa.accept_10_7_1_6_1_673 7 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 216 3 2 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 216 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 216 3 1 57 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 216
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 171 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 216)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 170 216
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 170 216 2 23 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 170 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 170 216 2 22 85 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 216 (accept_3_4 43
  170 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 216 2 21 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 216
  (Polychromatic418967fa.accept_15_11_5_6_1_669 41 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 170 216 2 20 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 170 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 170 216 2 19 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 170 216 (accept_3_4 37 170 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 170 216 2 18 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 170 216 (Polychromatic418967fa.accept_13_9_1_8_1_1742
  35 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 216 2 17 85 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 216
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 216 2 16 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 216 (accept_3_4 31 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 216 2 15 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 170 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 216 2 14 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 216
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 216 2 13 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 216 (accept_3_4 25 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 216 2 12 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 216 (Polychromatic418967fa.accept_25_23_20_16_1_12838 23 170 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 216 2 11 85 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 216
  (Polychromatic418967fa.accept_25_21_20_16_1_9215 21 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 170 216 2 10 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 170 216 (accept_3_4 19 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 216 2 9 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 170 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 216 2 8 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 216 2 7 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 216 (accept_3_4 13 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 216 2 6 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 170 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 216 2 5 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 216 2 4 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 216 (accept_3_4 7 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  216 2 3 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 216 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 170 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 216 2 2 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 216 2 1 85 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 216 (accept_3_4 1 170 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 216))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 169 216 (Eq.refl Bool.true) (allA_succ_of_accept 47 169 216 (accept_3_5 47 169 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 169 216 (Polychromatic418967fa.accept_25_21_19_16_1_11091 46 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 216 (accept_3_5 44 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 216 (Polychromatic418967fa.accept_25_17_19_16_1_11100 42 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 216 (accept_3_5 41 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 169 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 216
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 216 (accept_3_5 38 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 216 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 216 (accept_3_5 35 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 216 (Polychromatic418967fa.accept_19_15_17_7_1_8734 34 169
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 216 (accept_3_5 32 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 216 (Polychromatic418967fa.accept_16_15_9_8_1_2440 31 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 169 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 216 (accept_3_5 29 169 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 216 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 169 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 216
  (Polychromatic418967fa.accept_20_7_9_16_1_11410 27 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 169 216 (accept_3_5 26 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 169 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 169 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 216 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 169
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 216 (accept_3_5 23 169
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 216
  (Polychromatic418967fa.accept_23_22_8_9_1_12804 22 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 216 (accept_3_5 20 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 216
  (Polychromatic418967fa.accept_17_1_16_12_1_5298 18 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 169 216 (accept_3_5 17 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 169 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 169 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 169
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 216 (accept_3_5 14 169
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 13 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 169 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 216 (accept_3_5 11 169 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 169 216 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 216 (accept_3_5 8 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 216 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 216 (Polychromatic418967fa.accept_25_6_19_16_1_12800 6 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 216 (accept_3_5 5 169 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 216 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 169 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 216
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 216 (accept_3_5 2 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 216 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 169 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 216)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 168 216 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 168 216 24 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 216 (Polychromatic418967fa.accept_19_9_16_7_1_1056 47 168 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 216 2 23 84 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 216 3 15 56 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 216 4 11 42 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 216 6 7 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 168 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 216 8 5 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 216 3 13 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 216 2 19 84 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 216
  (Polychromatic418967fa.accept_11_4_3_7_1_828 37 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 216 12 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 216 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 168 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 216 2 17 84 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 216 3 11 56 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 216 8 4 21 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 216
  (Polychromatic418967fa.accept_13_5_12_8_1_198 31 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 216 6 5 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 168 216 (Polychromatic418967fa.accept_19_10_16_7_1_10039 29 168 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 216 4 7 42 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 216 3 9 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 216 2 13 84 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 216
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 216 24 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 168 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 216 2 11 84 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 216 3 7 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 216 4 5 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 216
  (Polychromatic418967fa.accept_25_19_18_16_1_9214 19 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 168 216 6 3 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 168 216 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 168 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 216 8 2 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 216 3 5 56 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 216 2 7 84 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 216
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 216 12 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 216 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 168 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 216 2 5 84 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 216 3 3 56 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 216 8 1 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 216
  (Polychromatic418967fa.accept_13_7_12_8_1_199 7 168 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 216 6 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 216 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 168 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 216 4 1 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 216 3 1 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 216 2 1 84 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 216 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 168 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  216))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 167 216 (Eq.refl Bool.true) (allA_succ_of_accept
  49 167 216 (accept_3_4 49 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 216
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 167 216 (Polychromatic418967fa.accept_14_5_13_6_1_3574 47 167 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 216 (accept_3_4 46 167 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 167 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 216
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 44 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 216 (accept_3_4 43 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 216 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 167 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 216 (accept_3_4 40 167 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 216 (Polychromatic418967fa.accept_21_18_20_6_1_6640 39 167 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 216
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 38 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 216 (accept_3_4 37 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 216 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 216 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 216 (accept_3_4 34 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 167
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 216
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 216 (accept_3_4 31 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 216 (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 216 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 216 (accept_3_4 28 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 167
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 216
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 167 216 (accept_3_4 25 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 167 216 (Polychromatic418967fa.accept_21_3_20_6_1_5126 24 167 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 167
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 216 (accept_3_4 22 167
  216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 167 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 167 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 216 (accept_3_4 19 167 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 167 216 (Polychromatic418967fa.accept_19_18_15_7_1_11442 18 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 216
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 216 (accept_3_4 16 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 216 (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 216 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 216 (accept_3_4 13 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 216 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 167
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 216
  (Polychromatic418967fa.accept_10_1_7_6_1_91 11 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 216 (accept_3_4 10 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 216 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 216 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 167 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 216 (accept_3_4 7 167 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 216 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 216
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 216 (accept_3_4 4 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 216 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 167 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 216 (Polychromatic418967fa.accept_21_2_20_6_1_2277 2 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 216 (accept_3_4 1 167 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 167 216)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 166
  216 (Eq.refl Bool.true) (allA_succ_of_gcd 50 166 216 2 25 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 216 (Polychromatic418967fa.accept_19_11_14_7_1_4473 49 166
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 166 216 2 24 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 166 216 (accept_3_5 47
  166 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 166 216 2 23 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 166 216
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 45 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 166 216 2 22 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 166 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 166 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 166 216 2 21 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 166 216 (accept_3_5 41 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 166 216 2 20 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 166 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 166 216 2 19 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 166 216 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 166 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 166 216 2 18 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 166 216 (accept_3_5 35 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 166 216 2 17 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 166 216
  (Polychromatic418967fa.accept_13_7_10_8_1_567 33 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 166 216 2 16 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 166 216 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 166 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 166 216 2 15 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 166 216 (accept_3_5 29 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 166 216 2 14 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 166 216
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 166 216 2 13 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 166 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 166 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 166 216 2 12 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 166 216 (accept_3_5 23 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 166 216 2 11 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 166 216
  (Polychromatic418967fa.accept_19_2_14_7_1_12783 21 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 166 216 2 10 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 166 216 (Polychromatic418967fa.accept_23_19_5_9_1_12822 19 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 166 216 2 9 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 166 216 (accept_3_5 17
  166 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 166 216 2 8 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 166 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 166 216 2 7 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 166 216 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 166 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 216 2 6 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 216 (accept_3_5 11 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 216 2 5 83 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 216
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 216 2 4 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 216 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 166 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 216 2 3 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 216 (accept_3_5 5 166 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166 216 2 2 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 166 216 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 166 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 216 2 1 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 216
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 166 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 166 216))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 165 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 165 216 3 17 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 165 216 (Polychromatic418967fa.accept_13_11_9_8_1_1125 50 165 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 49 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 216 3 16 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 165 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 216 (Polychromatic418967fa.accept_13_7_9_8_1_188
  46 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 216 3 15 55 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 216 (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 216 3 14 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 216 (Polychromatic418967fa.accept_10_1_5_6_1_649
  41 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 165 216 3 13 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 165 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 165 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 216 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 216 3 12 55 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 216
  (Polychromatic418967fa.accept_16_3_5_8_1_4543 35 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 216 3 11 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 216
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 32 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 165 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 216 3 10 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 216
  (Polychromatic418967fa.accept_10_9_5_6_1_691 29 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 216 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 216 3 9 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 216
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 165 216 3 8 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 165 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 216 (Polychromatic418967fa.accept_19_3_13_7_1_7245 22 165
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 216 3 7 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 216 3 6 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 165 216 3 5 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 165 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 216 (Polychromatic418967fa.accept_16_13_5_8_1_5814 13 165
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 216 3 4 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 216
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 216 3 3 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 216 (Polychromatic418967fa.accept_23_8_4_9_1_11208 8 165 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 216
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 216 3 2 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 165 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 216 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 165 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 216 3 1 55 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 165 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 216 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 165 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 216)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  164 216 (Eq.refl Bool.true) (allA_succ_of_gcd 52 164 216 4 13 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 164 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 164 216 2 25 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 164 216 (accept_3_4 49
  164 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 164 216 4 12 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 164 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 164 216 2 23 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 164 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 164 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 164 216 4 11 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 164 216 (accept_3_4 43 164 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 164 216 2 21 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 164 216 (Polychromatic418967fa.accept_16_9_4_8_1_2533
  41 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 216 4 10 41 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 216 2 19 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 216 (accept_3_4 37 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 216 4 9 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 164 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 216 2 17 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 216 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  33 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 216 4 8 41 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 216
  (accept_3_4 31 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 216 2 15 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 216
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 29 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 216 4 7 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 216 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 164 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 216 2 13 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 216 (accept_3_4 25 164 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 216 4 6 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 164 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 216 2 11 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 216
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 216 4 5 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 216 (accept_3_4 19 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 216 2 9 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 216 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 164 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 216 4 4 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 216 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 216 2 7 82 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 216
  (accept_3_4 13 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 216 4 3 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 216
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 216 2 5 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 164 216 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 216 4 2 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 216 (accept_3_4 7 164 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 216 2 3 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 216 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 164 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 216 4 1 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 216
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 216 2 1 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 216 (accept_3_4 1 164 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  216))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 163 216 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 163 216 (accept_3_5 53 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 216 (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 216 (accept_3_5 50 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 163
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 216
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 216 (accept_3_5 47 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 216 (accept_3_5 44 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 216
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 216 (accept_3_5 41 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 216 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 216 (accept_3_5 38 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 216
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 216 (accept_3_5 35 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 216 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 216 (Polychromatic418967fa.accept_19_14_11_7_1_7236 33 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 216 (accept_3_5 32 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 216
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 30 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 216 (accept_3_5 29 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 216 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 216 (accept_3_5 26 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 216
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 216 (accept_3_5 23 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 216 (Polychromatic418967fa.accept_16_5_3_8_1_4555 21 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 216 (accept_3_5 20 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 163
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 216
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 216 (accept_3_5 17 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 216 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 216 (accept_3_5 14 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 216 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 216
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 216 (accept_3_5 11 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 216 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 216 (accept_3_5 8 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 216 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 216
  (Polychromatic418967fa.accept_17_6_10_12_1_4129 6 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 216 (accept_3_5 5 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 216 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 216 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 216 (accept_3_5 2 163 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 216 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 162 216 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 162 216 54 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 216 (Polychromatic418967fa.accept_13_1_6_8_1_208 53 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 216 2 26 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 216 3 17 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 216 2 25 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 216
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 216 6 8 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 216 2 23 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 216 9 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 216 2 22 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 216
  (Polychromatic418967fa.accept_19_5_10_7_1_5887 43 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 216 6 7 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 216 2 20 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 216 3 13 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 216 2 19 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 216
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 216 18 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 216 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 216 2 17 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 216 3 11 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 216 2 16 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 216
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 216 6 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 216 (Polychromatic418967fa.accept_21_8_15_6_1_8247 29 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 216 2 14 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 216 27 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 216 2 13 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 216
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 162 216 6 4 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 216 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 162 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 216 2 11 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 216 3 7 54 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 216 2 10 81 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 216
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 216 18 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 216 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 216 2 8 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 216 3 5 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 216 2 7 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 216
  (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 216 6 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 162 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 216 2 5 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 216 9 1 18 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 216 2 4 81 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 216
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 216 6 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 216 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 216 2 2 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 216 3 1 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 216 2 1 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 216 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  162 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  216))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 161 216 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 161 216 (accept_3_4 55 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 54 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 216 (Polychromatic418967fa.accept_13_1_5_8_1_207 53 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 216 (accept_3_4 52 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 216 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 216
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 216 (accept_3_4 49 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 48 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 47 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 216 (accept_3_4 46 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 216
  (Polychromatic418967fa.accept_16_12_1_8_1_5767 44 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 216 (accept_3_4 43 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 216 (Polychromatic418967fa.accept_14_13_7_6_1_3525 41 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 216 (accept_3_4 40 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 216
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 216 (accept_3_4 37 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 216 (accept_3_4 34 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 216 (accept_3_4 31 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 216 (Polychromatic418967fa.accept_19_11_9_7_1_4447 30 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 216 (accept_3_4 28 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 216
  (Polychromatic418967fa.accept_20_6_1_16_1_4059 26 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 216 (accept_3_4 25 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 216 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 216 (accept_3_4 22 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 216 (Polychromatic418967fa.accept_17_4_8_12_1_9165 21 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 216
  (Polychromatic418967fa.accept_15_5_11_6_1_692 20 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 216 (accept_3_4 19 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 216 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 216 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 216 (accept_3_4 16 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 161
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 216
  (Polychromatic418967fa.accept_13_1_5_8_1_207 14 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 216 (accept_3_4 13 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 216 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 216 (Polychromatic418967fa.accept_19_11_9_7_1_4447 11 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 216 (accept_3_4 10 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 216 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 161 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 216
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 216 (accept_3_4 7 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 216 (Polychromatic418967fa.accept_20_6_1_16_1_4059 6 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 216 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 161 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 216 (accept_3_4 4 161 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 216 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 161 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 216
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 216 (accept_3_4 1 161 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  216)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 160 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 160 216 8 7 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 160 216 (Polychromatic418967fa.accept_17_4_7_12_1_6556 55 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 160 216 2 27 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 216 (accept_3_5 53 160 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 216 4 13 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 216 (Polychromatic418967fa.accept_13_12_4_8_1_1120 51 160
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 216 2 25 80 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 216
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 216 8 6 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 160 216 (accept_3_5 47 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  160 216 2 23 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 160 216 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 216 4 11 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 216
  (Polychromatic418967fa.accept_26_17_4_8_1_12814 43 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 216 2 21 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 216 (accept_3_5 41 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 216 8 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 160 216 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 216 2 19 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 216 (Polychromatic418967fa.accept_13_11_4_8_1_1098
  37 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 216 4 9 40 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 216
  (accept_3_5 35 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 216 2 17 80 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 216
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 216 8 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 216 (Polychromatic418967fa.accept_15_1_10_6_1_631 31 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 216 2 15 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 216 (accept_3_5 29 160 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 216 4 7 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 216 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 160
  216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 216 2 13 80 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 216
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 216 8 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 160 216 (accept_3_5 23 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  160 216 2 11 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 160 216 (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 216 4 5 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 216 (Polychromatic418967fa.accept_15_4_10_6_1_2997
  19 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 216 2 9 80 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 216
  (accept_3_5 17 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 216 8 2 20 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 216
  (Polychromatic418967fa.accept_19_15_8_7_1_11482 15 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 160 216 2 7 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 160 216 (Polychromatic418967fa.accept_22_13_6_18_1_12837 13 160 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 216 4 3 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 216 (accept_3_5 11
  160 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 216 2 5 80 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 216
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 216 8 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 216 (Polychromatic418967fa.accept_21_7_13_6_1_349 7 160 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 216 2 3 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 216 (accept_3_5 5 160 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 216 4 1 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 216 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 160 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 216 2 1 80 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 216
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 160 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 159 216 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 159 216 3 19 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 159 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 216
  (Polychromatic418967fa.accept_10_5_9_6_1_697 55 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 216 3 18 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 159 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 216
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 159 216 3 17 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 159 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 216 (Polychromatic418967fa.accept_15_4_9_6_1_627
  49 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 216 3 16 53 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 216
  (Polychromatic418967fa.accept_21_5_12_6_1_11321 47 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 159 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 159 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 216 3 15 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 216
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 216 3 14 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 216 (Polychromatic418967fa.accept_14_13_5_6_1_2747
  41 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 216
  (Polychromatic418967fa.accept_21_19_12_6_1_6689 40 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 159 216 3 13 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 159 216 (Polychromatic418967fa.accept_21_17_12_6_1_12761 38 159 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 216
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 159 216 3 12 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 35 159 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 216 (Polychromatic418967fa.accept_15_4_9_6_1_627
  34 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 216 3 11 53 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 216 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 216 3 10 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 216
  (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 159 216 3 9 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 159 216 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 159 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 216 3 8 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 159 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 216 3 7 53 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 216
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 216 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 216 3 6 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 216 (Polychromatic418967fa.accept_16_1_15_8_1_2411
  17 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 216
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 216 3 5 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 216 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 216 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 159 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 216 3 4 53 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 216
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 216 (Polychromatic418967fa.accept_17_10_6_12_1_11635 10 159 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 216 3 3 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 8
  159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 216
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 216 3 2 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 216 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 216 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 216
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 216 3 1 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 216
  (Polychromatic418967fa.accept_17_2_6_12_1_7912 2 159 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 216 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 216 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 216))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 158 216 (Eq.refl Bool.true) (allA_succ_of_gcd 58 158 216 2 29 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 216
  (Polychromatic418967fa.accept_21_15_11_6_1_5121 57 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 158 216 2 28 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 158 216 (accept_3_4 55 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 216 2 27 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 216 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 158 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 216 2 26 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 216 2 25 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 216 (accept_3_4 49 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 216 2 24 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 158 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 216 2 23 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 216
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 216 2 22 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 216 (accept_3_4 43 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 216 2 21 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 216 (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 158 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 216 2 20 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 216
  (Polychromatic418967fa.accept_19_1_6_7_1_2019 39 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 216 2 19 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 216 (accept_3_4 37 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 216 2 18 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 216 (Polychromatic418967fa.accept_19_16_6_7_1_4425 35 158 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 216 2 17 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 216
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 216 2 16 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 216 (accept_3_4 31 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 216 2 15 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 216 (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 158 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 216 2 14 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 216
  (Polychromatic418967fa.accept_17_10_5_12_1_4101 27 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 158 216 2 13 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 158 216 (accept_3_4 25 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 216 2 12 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 216 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 158 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 216 2 11 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 216
  (Polychromatic418967fa.accept_20_1_18_16_1_12711 21 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 158 216 2 10 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 158 216 (accept_3_4 19 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 216 2 9 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 158 216 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 216 2 8 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 216
  (Polychromatic418967fa.accept_20_15_18_16_1_5441 15 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 158 216 2 7 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 158 216 (accept_3_4 13 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 216 2 6 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 216 (Polychromatic418967fa.accept_20_11_18_16_1_1559 11 158 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 216 2 5 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 216
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 216 2 4 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 216 (accept_3_4 7 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  216 2 3 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 216 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 216 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 216 2 2 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 216 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 216 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 216 2 1 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 216 (accept_3_4 1 158 216
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 216)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_216_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


