-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch230
-- name    : Polychromatic418967fa_Branch230
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:26:27.030899+00:00
-- url     : https://prove2.me/theorems/83d4321e-3825-4b83-8d3d-56aa9a6c8b9b
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch230_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_230 : allB 230 230 :=
  allB_succ' 2 229 230 (Eq.refl Bool.true) (allA_of_3_0 2 229 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  228 230 (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 230 2 1 114 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 230 (accept_3_2 1 228 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 230))) (allB_succ' 4 227 230 (Eq.refl Bool.true) (allA_succ_of_accept 3 227 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 227 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 227 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 230 (accept_3_2 1 227 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 227 230)))) (allB_succ' 5 226 230 (Eq.refl Bool.true) (allA_of_3_0 5 226 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 225 230 (Eq.refl Bool.true) (allA_succ_of_gcd 5 225 230 5 1 45 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 230 (accept_3_2 4
  225 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 225 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 230 (accept_3_2 1 225 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 230)))))) (allB_succ' 7 224 230 (Eq.refl Bool.true) (allA_succ_of_gcd 6 224 230 2 3 112 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 224 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 224 230 2 2 112 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 224 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 224 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 230 2 1 112 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 230 (accept_3_2 1 224 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 224 230))))))) (allB_succ' 8 223 230 (Eq.refl Bool.true) (allA_of_3_0 8 223
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 222 230 (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 230 2 4
  111 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 230
  (accept_3_2 7 222 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 230 2 3 111 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 230
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 222 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 230 2 2 111 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 222 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 230 2 1 111 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 230 (accept_3_2 1 222 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 222 230))))))))) (allB_succ' 10 221 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 221 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 221 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 230 (accept_3_2 7 221 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 230 (Polychromatic418967fa.accept_15_6_11_5_1_168
  6 221 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 221 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 230 (accept_3_2 4 221 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 221 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 230 (accept_3_2 1 221 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 230)))))))))) (allB_succ' 11 220 230 (Eq.refl Bool.true) (allA_of_3_0 11 220 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 219 230 (Eq.refl Bool.true) (allA_succ_of_accept 11 219 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 230 (accept_3_2 10 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 219 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 230 (accept_3_2 7 219 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 219 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 230 (accept_3_2 4 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 219 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 230 (accept_3_2 1 219 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 230)))))))))))) (allB_succ' 13 218 230 (Eq.refl Bool.true) (allA_succ_of_gcd 12 218
  230 2 6 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 218 230 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 218 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 218 230 2 5 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 218 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 218 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 218 230 2 4 109 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 218 230 (accept_3_2 7 218 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 218 230 2 3 109 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 218 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 218 230 2 2 109 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 218 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 218 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 218 230 2 1 109 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 218 230 (accept_3_2 1 218 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 230))))))))))))) (allB_succ' 14 217 230 (Eq.refl Bool.true) (allA_of_3_0
  14 217 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 216 230 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  216 230 2 7 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 216 230 (accept_3_2 13 216 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  216 230 2 6 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 230 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 216 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 230 2 5 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 230 (Polychromatic418967fa.accept_19_9_7_2_1_6868 9
  216 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 230 2 4 108 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 230 (accept_3_2 7
  216 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 230 2 3 108 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 230
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 5 216 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 216 230 2 2 108 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 216 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 216 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 230 2 1 108 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 230 (accept_3_2 1 216 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 230))))))))))))))) (allB_succ' 16 215 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 215 230 5 3 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 215 230 (Polychromatic418967fa.accept_20_14_15_10_1_3554 14 215 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 230 (accept_3_2 13 215 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 215 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 215 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 215 230 5 2 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 215 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 215 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 230 (accept_3_2 7 215 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6
  215 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 215 230 5 1 43 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 215 230 (accept_3_2 4
  215 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 215 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 215 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 230 (accept_3_2 1 215 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 215 230)))))))))))))))) (allB_succ' 17 214 230 (Eq.refl Bool.true) (allA_of_3_0 17 214 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 213 230 (Eq.refl Bool.true) (allA_succ_of_accept 17 213 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 230 (accept_3_2 16 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 213 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 230 (accept_3_2 13 213 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 213 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 230 (accept_3_2 10 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 213 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 230 (accept_3_2 7 213 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 213 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 230 (accept_3_2 4 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 213 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 230 (accept_3_2 1 213 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 230)))))))))))))))))) (allB_succ' 19 212 230 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 212 230 2 9 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 212 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 212 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 230 2 8 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  212 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 212 230 2 7 106 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 212 230 (accept_3_2 13
  212 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 212 230 2 6 106 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 212 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 212 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 212 230 2 5 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 212 230 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 212 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 230 2 4 106 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 230 (accept_3_2 7 212 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 230 2 3 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5
  212 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 230 2 2 106 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 212 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 230 2 1 106 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 230 (accept_3_2 1 212 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  230))))))))))))))))))) (allB_succ' 20 211 230 (Eq.refl Bool.true) (allA_of_3_0 20 211 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 210 230 (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 230 10 2 21 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 230 (accept_3_2 19 210 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 230 2 9 105 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 210 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 230 2 8 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 210 230 5 3 42 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 210 230 2 7 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 210 230 (accept_3_2 13 210 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 230 2 6 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 210 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 230 10 1 21 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 230
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 210 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 230 2 4 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 230 (accept_3_2 7 210 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 230 2 3 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 210 230 5 1 42 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 210 230 2 2 105 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 210 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 210 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 230 2 1 105 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 230 (accept_3_2 1 210 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 230))))))))))))))))))))) (allB_succ' 22 209 230 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 209 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 230 (Polychromatic418967fa.accept_12_8_5_2_1_746
  20 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 230 (accept_3_2 19
  209 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 230
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 209 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 209 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 230 (accept_3_2 16 209 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 209 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 230
  (Polychromatic418967fa.accept_17_14_5_9_1_7766 14 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 230 (accept_3_2 13 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 230 (accept_3_2 10 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 230 (accept_3_2 7 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 230 (accept_3_2 4 209 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 230
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 230 (accept_3_2 1 209 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  230)))))))))))))))))))))) (allB_succ' 23 208 230 (Eq.refl Bool.true) (allA_of_3_0 23 208 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 207 230 (Eq.refl Bool.true) (allA_succ_of_gcd 23 207 230 23 1 9 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 207 230 (accept_3_2 22
  207 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 207 230 (Polychromatic418967fa.accept_25_20_7_5_1_13759 20 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 230 (accept_3_2 19 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 207 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 230 (accept_3_2 16 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 230 (Polychromatic418967fa.accept_19_15_17_2_1_4097 15 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 230 (Polychromatic418967fa.accept_19_14_17_2_1_1720 14 207 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 230 (accept_3_2 13 207 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 230 (accept_3_2 10 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 230 (accept_3_2 7 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 207 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 230 (accept_3_2 4 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 230 (accept_3_2 1 207 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 230)))))))))))))))))))))))) (allB_succ' 25 206 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 206 230 2 12 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 206 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 230 2 11 103 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 230 2 10 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 230 (accept_3_2 19 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 230 2 9 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 206 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 230 2 8 103 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 230 2 7 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 230 (accept_3_2 13 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 230 2 6 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 206 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 230 2 5 103 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 230 2 4 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 230 (accept_3_2 7 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 230 2 3 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 206 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 230 2 2 103 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 230 2 1 103 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 230 (accept_3_2 1 206 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  230))))))))))))))))))))))))) (allB_succ' 26 205 230 (Eq.refl Bool.true) (allA_of_3_0 26 205 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 204 230 (Eq.refl Bool.true) (allA_succ_of_gcd 26 204 230 2 13 102 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 230 (accept_3_2 25
  204 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 230 2 12 102 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 204 230 2 11 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 204 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 204 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 230 2 10 102 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 230 (accept_3_2 19 204 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 230 2 9 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  204 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 230 2 8 102 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 230
  (Polychromatic418967fa.accept_20_15_4_10_1_9538 15 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 204 230 2 7 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 204 230 (accept_3_2 13 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 230 2 6 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 204 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 230 2 5 102 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 204 230 2 4 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 204 230 (accept_3_2 7 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 230 2 3 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 204 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 230 2 2 102 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 230 2 1 102 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 230 (accept_3_2 1 204 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  230))))))))))))))))))))))))))) (allB_succ' 28 203 230 (Eq.refl Bool.true) (allA_succ_of_accept 27 203 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 203 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 203 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 230 (accept_3_2 25 203 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 203 230 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 230
  (Polychromatic418967fa.accept_17_6_16_9_1_5129 23 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 230 (accept_3_2 22 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 230 (accept_3_2 19 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 230 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 203
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 230 (accept_3_2 16 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 230 (accept_3_2 13 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 230 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 203
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 230
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 230 (accept_3_2 10 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 230 (accept_3_2 7 203 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 203
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 230 (accept_3_2 4 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 230 (Polychromatic418967fa.accept_16_2_11_6_1_737 2 203 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 230 (accept_3_2 1 203 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 230)))))))))))))))))))))))))))) (allB_succ' 29 202 230 (Eq.refl Bool.true)
  (allA_of_3_0 29 202 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 201 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 201 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 230 (accept_3_2 28 201 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 230 (Polychromatic418967fa.accept_9_8_3_5_1_241
  26 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 230 (accept_3_2 25
  201 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 230 (accept_3_2 22 201 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 230 (Polychromatic418967fa.accept_17_4_14_9_1_5105 21 201 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 230 (accept_3_2 19 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 230 (accept_3_2 16 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 230 (accept_3_2 13 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 230 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 230 (accept_3_2 10 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 230 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 201 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 230 (accept_3_2 7 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 230 (accept_3_2 4 201 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 230 (accept_3_2 1 201 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  230)))))))))))))))))))))))))))))) (allB_succ' 31 200 230 (Eq.refl Bool.true) (allA_succ_of_gcd 30 200 230 10 3 20 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 200 230 2 14 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 200 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 200 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 230 2 13 100 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 200 230 5 5 40 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 200 230 2 12 100 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 200 230 2 11 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 200 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 200 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 230 10 2 20 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 230 (accept_3_2 19 200 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 230 2 9 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  200 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 230 2 8 100 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 200 230 5 3 40 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 200 230 2 7 100 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 230
  (accept_3_2 13 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 230 2 6 100 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 200 230 10 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 200 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 200 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 230 2 4 100 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 230 (accept_3_2 7 200 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 230 2 3 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 200 230 5 1 40 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 200 230 2 2 100 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 230 2 1 100 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 230 (accept_3_2 1 200 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  230))))))))))))))))))))))))))))))) (allB_succ' 32 199 230 (Eq.refl Bool.true) (allA_of_3_0 32 199 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 198 230 (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 230 2 16 99 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 230
  (accept_3_2 31 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 230 2 15 99 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 230 2 14 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 198 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 230 2 13 99 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 230 (accept_3_2 25 198 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 230 2 12 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 230 (Polychromatic418967fa.accept_15_8_3_5_1_608
  23 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 230 2 11 99 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 230 2 10 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 230 (accept_3_2 19 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 230 2 9 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 198 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 230 2 8 99 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 230 2 7 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 230 (accept_3_2 13 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 230 2 6 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 198 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 230 2 5 99 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 230 2 4 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 230 (accept_3_2 7 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  230 2 3 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 230 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 198 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 230 2 2 99 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 198 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 230 2 1 99 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 230 (accept_3_2 1 198 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 230))))))))))))))))))))))))))))))))) (allB_succ' 34 197 230
  (Eq.refl Bool.true) (allA_succ_of_accept 33 197 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 230 (accept_3_2 31 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 230 (accept_3_2 28 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 230 (accept_3_2 25 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 230 (accept_3_2 22 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 230 (accept_3_2 19 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 230 (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 230 (accept_3_2 16 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 230 (accept_3_2 13 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 230 (accept_3_2 10 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 230 (accept_3_2 7 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 230 (accept_3_2 4 197 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 230 (accept_3_2 1 197 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  230)))))))))))))))))))))))))))))))))) (allB_succ' 35 196 230 (Eq.refl Bool.true) (allA_of_3_0 35 196 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 195 230 (Eq.refl Bool.true) (allA_succ_of_gcd 35 195 230 5 7 39 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 230
  (accept_3_2 34 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 230 (Polychromatic418967fa.accept_20_12_15_10_1_6520 32 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 230 (accept_3_2 31 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 230 5 6 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 230 (accept_3_2 28 195 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 230
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 195 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 230 5 5 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 195 230
  (Polychromatic418967fa.accept_20_4_15_10_1_6519 24 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 230 (accept_3_2 22 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 195 230 5 4 39 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 195 230 (accept_3_2 19 195 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 230 (Polychromatic418967fa.accept_12_6_3_2_1_743
  18 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 230 (accept_3_2 16 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  195 230 5 3 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 195 230 (Polychromatic418967fa.accept_19_14_5_2_1_6941 14 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 230 (accept_3_2 13 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 195 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 195 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 195 230 5 2 39 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 195 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 195 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 230 (accept_3_2 7 195 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 230 5 1 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 230 (accept_3_2 4 195 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 195 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 230 (accept_3_2 1 195 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  230)))))))))))))))))))))))))))))))))))) (allB_succ' 37 194 230 (Eq.refl Bool.true) (allA_succ_of_gcd 36 194 230 2 18
  97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 194 230
  (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 194 230 2 17 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 194 230 (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 194 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 194 230 2 16 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 194 230 (accept_3_2 31 194 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 194 230 2 15 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 194 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 194 230 2 14 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 194 230 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 194 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 194 230 2 13 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 194 230 (accept_3_2 25 194 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 194 230 2 12 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 194 230
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 194 230 2 11 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 194 230 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 194 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 194 230 2 10 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 194 230 (accept_3_2 19 194 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 194 230 2 9 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 194 230
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 194 230 2 8 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 194 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 194 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 194 230 2 7 97 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 194 230 (accept_3_2 13 194 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 194 230 2 6 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 194 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 230 2 5 97 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 230
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 230 2 4 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 230 (accept_3_2 7 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  230 2 3 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 230 (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 194 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 230 2 2 97 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 194 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 230 2 1 97 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 230 (accept_3_2 1 194 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 230))))))))))))))))))))))))))))))))))))) (allB_succ' 38 193 230
  (Eq.refl Bool.true) (allA_of_3_0 38 193 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 192 230 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 192 230 2 19 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 192 230 (accept_3_2 37 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 230 2 18 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 192 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 230 2 17 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 230 2 16 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 192 230 (accept_3_2 31 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 230 2 15 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 192 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 230 2 14 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 230
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 230 2 13 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 230 (accept_3_2 25 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 230 2 12 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 192 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 230 2 11 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 230
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 230 2 10 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 192 230 (accept_3_2 19 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 230 2 9 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 230 2 8 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 230 2 7 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 230 (accept_3_2 13 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 230 2 6 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 192 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 230 2 5 96 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 230 2 4 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 230 (accept_3_2 7 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  230 2 3 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 230 (Polychromatic418967fa.accept_20_5_12_10_1_5072 5 192 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 230 2 2 96 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 192 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 230 2 1 96 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 230 (accept_3_2 1 192 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 230))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 191
  230 (Eq.refl Bool.true) (allA_succ_of_accept 39 191 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 230 (accept_3_2 37 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 230 (accept_3_2 34 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 230 (accept_3_2 31 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 230 (accept_3_2 28 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 230 (accept_3_2 25 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 230 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 230 (accept_3_2 22 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 230 (accept_3_2 19 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 230 (accept_3_2 16 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 230
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 14 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 230 (accept_3_2 13 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 230 (accept_3_2 10 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 230 (accept_3_2 7 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 230 (accept_3_2 4 191 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 230
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 230 (accept_3_2 1 191 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  230)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 190 230 (Eq.refl Bool.true) (allA_of_3_0 41 190 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 189 230 (Eq.refl Bool.true) (allA_succ_of_accept 41 189 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 230 (accept_3_2 40 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 230 (Polychromatic418967fa.accept_17_4_2_9_1_3896 38 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 230 (accept_3_2 37 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 189
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 230 (accept_3_2 34 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 230 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 230 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 230 (accept_3_2 31 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 189
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 230 (accept_3_2 28 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 230 (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 230 (accept_3_2 25 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 230 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 189
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 230 (accept_3_2 22 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 230 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 230 (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 230 (accept_3_2 19 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 189
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 230 (accept_3_2 16 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 230 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 230 (accept_3_2 13 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 189
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 230 (accept_3_2 10 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 230 (Polychromatic418967fa.accept_16_9_13_6_1_2334 9 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 230 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 189 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 230 (accept_3_2 7 189 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 230 (accept_3_2 4 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 230 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 189 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 230 (accept_3_2 1 189 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 230)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 188 230 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 188 230 2 21 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 188 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 188 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 230 2 20 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 230 2 19 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 230 (accept_3_2 37 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 230 2 18 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 188 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 230 2 17 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 230 2 16 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 188 230 (accept_3_2 31 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 230 2 15 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 188 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 230 2 14 94 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 230 2 13 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 230 (accept_3_2 25 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 230 2 12 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 188 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 230 2 11 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 230 2 10 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 230 (accept_3_2 19 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 230 2 9 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 188 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 230 2 8 94 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 230 2 7 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 230 (accept_3_2 13 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 230 2 6 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 188 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 230 2 5 94 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 230
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 230 2 4 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 230 (accept_3_2 7 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  230 2 3 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 188 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 230 2 2 94 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 188 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 230 2 1 94 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 230 (accept_3_2 1 188 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 230))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  187 230 (Eq.refl Bool.true) (allA_of_3_0 44 187 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 186 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 186 230 2 22 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 230 (accept_3_2 43 186 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 186 230 2 21 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 186 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 186 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 230 2 20 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 230 2 19 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 230 (accept_3_2 37 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 230 2 18 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 186 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 230 2 17 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 230 2 16 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 230 (accept_3_2 31 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 230 2 15 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 186 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 230 2 14 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 230 2 13 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 230 (accept_3_2 25 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 230 2 12 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 186 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 230 2 11 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 230 2 10 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 230 (accept_3_2 19 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 230 2 9 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 186 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 230 2 8 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 230 2 7 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 230 (accept_3_2 13 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 230 2 6 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 186 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 230 2 5 93 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 230 2 4 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 230 (accept_3_2 7 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  230 2 3 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 186 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 230 2 2 93 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 186 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 230 2 1 93 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 230 (accept_3_2 1 186 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 230))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  185 230 (Eq.refl Bool.true) (allA_succ_of_gcd 45 185 230 5 9 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 185 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 230 (accept_3_2 43 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 230
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 185 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 185 230 5 8 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 185 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 230
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 38 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 230 (accept_3_2 37 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 230 (Polychromatic418967fa.accept_19_17_14_2_1_4116 36 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 185 230 5 7 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 185 230 (accept_3_2 34 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 185 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 230 (accept_3_2 31 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 185 230 5 6 37 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 185 230
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 230 (accept_3_2 28 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 230 (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 185 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 185 230 5 5 37 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 185 230
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 230 (accept_3_2 22 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 185 230 5 4 37 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 185 230 (accept_3_2 19 185 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 230
  (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 185 230 (accept_3_2 16 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 185 230 5 3 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 185 230 (Polychromatic418967fa.accept_20_14_5_10_1_3647 14 185 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 230 (accept_3_2 13 185 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 185 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 185 230 5 2 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 185 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 230 (accept_3_2 7 185 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 230 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  6 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 230 5 1 37 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 230 (accept_3_2 4
  185 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 230 (accept_3_2 1 185 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185 230)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 184 230 (Eq.refl Bool.true)
  (allA_of_3_0 47 184 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 183 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 183 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 230 (accept_3_2 46 183 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 230 (Polychromatic418967fa.accept_7_2_1_6_1_173
  44 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 230 (accept_3_2 43
  183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 42 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 183 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 230 (accept_3_2 40 183 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 230 (accept_3_2 37 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 230 (accept_3_2 34 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 230
  (Polychromatic418967fa.accept_13_6_1_9_1_619 32 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 230 (accept_3_2 31 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 230 (accept_3_2 28 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 230 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 183 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 230 (accept_3_2 25 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 230 (accept_3_2 22 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 230 (accept_3_2 19 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 230 (accept_3_2 16 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 230
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 230 (accept_3_2 13 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 230 (accept_3_2 10 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 230 (accept_3_2 7 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 230 (accept_3_2 4 183 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 183 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 230 (accept_3_2 1 183 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  230)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 182 230 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  182 230 2 24 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 182 230 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 182 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 230 2 23 91 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 230
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 45 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 230 2 22 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 230 (accept_3_2 43 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 230 2 21 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 230 (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 182 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 230 2 20 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 230 2 19 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 230 (accept_3_2 37 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 230 2 18 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 182 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 230 2 17 91 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 182 230 2 16 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 182 230 (accept_3_2 31 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 230 2 15 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 230 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 182 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 230 2 14 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 230
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 230 2 13 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 230 (accept_3_2 25 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 230 2 12 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 230 (Polychromatic418967fa.accept_19_4_11_2_1_11111 23 182 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 230 2 11 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 230 2 10 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 230 (accept_3_2 19 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 230 2 9 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 182 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 230 2 8 91 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 230 2 7 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 230 (accept_3_2 13 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 230 2 6 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 230 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 182 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 230 2 5 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 230
  (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 230 2 4 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 230 (accept_3_2 7 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  230 2 3 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 182 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 230 2 2 91 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 182 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 230 2 1 91 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 230 (accept_3_2 1 182 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 230)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 181 230 (Eq.refl Bool.true) (allA_of_3_0 50 181 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 180 230 (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 230 10 5 18 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 230 (accept_3_2 49 180 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 180 230 2 24 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 180 230 (Polychromatic418967fa.accept_13_8_11_9_1_593
  47 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 230 2 23 90 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 230 5 9 36 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 230 2 22 90
  115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 230
  (accept_3_2 43 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 180 230 2 21 90 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 180 230
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 230 10 4 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 180 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 230 2 19 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 230 (accept_3_2 37 180 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 230 2 18 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 180 230 5 7 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 230 2 17 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 230
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 180 230 2 16 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 180 230 (accept_3_2 31 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 230 10 3 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 180 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 230 2 14 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 230 2 13 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 180 230 5 5 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 180 230 2 12 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 230 (Polychromatic418967fa.accept_19_4_9_2_1_8342 23 180 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 230 2 11 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 230
  (Polychromatic418967fa.accept_13_8_11_9_1_593 21 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 230 10 2 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 180 230 (accept_3_2 19 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 230 2 9 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 230 (Polychromatic418967fa.accept_19_17_9_2_1_12492 17 180 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 230 2 8 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 230 5 3 36 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 230 2 7 90 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 230 (accept_3_2 13
  180 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 230 2 6 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 230 10 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 230 (Polychromatic418967fa.accept_21_9_12_20_1_10792 9 180 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 230 2 4 90 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 230 (accept_3_2 7 180 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 230 2 3 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 230 5 1 36 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 230 2 2 90 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 230
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 230 2 1 90 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 230 (accept_3_2 1 180 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  230))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 179 230 (Eq.refl Bool.true) (allA_succ_of_accept
  51 179 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 230 (Polychromatic418967fa.accept_16_2_3_6_1_3372 50 179 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 230 (accept_3_2 49 179 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 179 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 230 (accept_3_2 46 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 230 (accept_3_2 43 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 179 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 230 (accept_3_2 40 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 230 (accept_3_2 37 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 230 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 179 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 230
  (Polychromatic418967fa.accept_20_15_19_10_1_11039 35 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 179 230 (accept_3_2 34 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 179
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 230 (accept_3_2 31 179
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 230 (accept_3_2 28 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 179 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 230 (Polychromatic418967fa.accept_7_5_4_6_1_167
  26 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 230 (accept_3_2 25
  179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 179 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 230 (accept_3_2 22 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 230 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 230 (accept_3_2 19
  179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 230
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 230 (accept_3_2 16 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 179 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 230 (Polychromatic418967fa.accept_13_1_10_9_1_215
  14 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 230 (accept_3_2 13
  179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 179 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 230 (accept_3_2 10 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  8 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 230 (accept_3_2 7
  179 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 179 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 230 (accept_3_2 4 179 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 179 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  179 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 230 (accept_3_2 1 179
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179 230))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 178 230 (Eq.refl Bool.true) (allA_of_3_0 53 178 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 54 177 230 (Eq.refl Bool.true) (allA_succ_of_accept 53 177 230 (Polychromatic418967fa.accept_6_5_3_2_1_68
  53 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 230 (accept_3_2 52
  177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 177 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 177 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 230 (accept_3_2 49 177 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 177 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 230 (accept_3_2 46
  177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 177 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 177 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 230 (accept_3_2 43 177 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 177 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 230 (accept_3_2 40 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 230 (accept_3_2 37 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 230 (accept_3_2 34 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 230 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 230 (accept_3_2 31 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 230 (accept_3_2 28 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 230 (accept_3_2 25 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 230 (accept_3_2 22 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 230 (accept_3_2 19 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 230 (accept_3_2 16 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 230 (accept_3_2 13 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 177 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 230 (accept_3_2 10 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 230 (accept_3_2 7 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 177 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 230 (accept_3_2 4 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 230 (accept_3_2 1 177 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 230)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 176 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 176 230 2 27 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 176 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 230 2 26 88 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 230 2 25 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 230 (accept_3_2 49 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 230 2 24 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 176 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 230 2 23 88 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 230
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 230 2 22 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 230 (accept_3_2 43 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 230 2 21 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 176 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 230 2 20 88 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 230
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 39 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 230 2 19 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 230 (accept_3_2 37 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 230 2 18 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 176 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 176 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 230 2 17 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 230 2 16 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 230 (accept_3_2 31 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 230 2 15 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 176 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 230 2 14 88 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 230
  (Polychromatic418967fa.accept_19_8_5_2_1_4105 27 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 230 2 13 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 230 (accept_3_2 25 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 230 2 12 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 176 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 230 2 11 88 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 230
  (Polychromatic418967fa.accept_13_8_7_9_1_611 21 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 230 2 10 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 230 (accept_3_2 19 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 230 2 9 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 176 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 230 2 8 88 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 230
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 230 2 7 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 230 (accept_3_2 13 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 230 2 6 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 176 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 230 2 5 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 230 2 4 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 230 (accept_3_2 7 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  230 2 3 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 176 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 230 2 2 88 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 230 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 176 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 230 2 1 88 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 230 (accept_3_2 1 176 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 175 230 (Eq.refl Bool.true) (allA_of_3_0 56 175 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 174 230 (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 230 2 28 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 230 (accept_3_2 55 174 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 230 2 27 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 53
  174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 230 2 26 87 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 230 2 25 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 230 (accept_3_2 49 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 230 2 24 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 174 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 230 2 23 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 230
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 230 2 22 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 230 (accept_3_2 43 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 230 2 21 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 174 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 230 2 20 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 230 2 19 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 230 (accept_3_2 37 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 230 2 18 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 174 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 230 2 17 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 230 2 16 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 230 (accept_3_2 31 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 230 2 15 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 174 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 230 2 14 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 230 2 13 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 230 (accept_3_2 25 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 230 2 12 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 174 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 230 2 11 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 230 2 10 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 230 (accept_3_2 19 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 230 2 9 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 174 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 230 2 8 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 230 2 7 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 230 (accept_3_2 13 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 230 2 6 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 174 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 230 2 5 87 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 230 2 4 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 230 (accept_3_2 7 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  230 2 3 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 230 (Polychromatic418967fa.accept_19_5_3_2_1_2867 5 174 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 230 2 2 87 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 174 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 230 2 1 87 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 230 (accept_3_2 1 174 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 173 230 (Eq.refl Bool.true) (allA_succ_of_accept 57 173 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 230 (accept_3_2 55 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 230 (Polychromatic418967fa.accept_24_6_5_14_1_13735 54 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 230 (accept_3_2 52 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 230 (accept_3_2 49 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 230 (accept_3_2 46 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 230 (accept_3_2 43 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 230 (Polychromatic418967fa.accept_14_13_5_6_1_2747 41 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 230 (accept_3_2 40 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 230
  (Polychromatic418967fa.accept_18_2_11_14_1_69 38 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 230 (accept_3_2 37 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 230 (accept_3_2 34 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 230 (accept_3_2 31 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 230 (accept_3_2 28 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 230 (accept_3_2 25 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 230 (accept_3_2 22 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 230
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 230 (accept_3_2 19 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 230 (accept_3_2 16 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 230
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 230 (accept_3_2 13 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 230 (accept_3_2 10 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 230 (accept_3_2 7 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 230 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 230 (accept_3_2 4 173 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 230
  (Polychromatic418967fa.accept_18_2_11_14_1_69 2 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 230 (accept_3_2 1 173 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 172 230 (Eq.refl Bool.true) (allA_of_3_0
  59 172 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 171 230 (Eq.refl Bool.true) (allA_succ_of_accept 59
  171 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 171 230 (accept_3_2 58 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 171 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 171
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 230 (accept_3_2 55 171
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 230
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 171 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 230 (accept_3_2 52 171 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 230
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 50 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 230 (accept_3_2 49 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 171 230 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 171 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 230 (accept_3_2 46 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 230 (accept_3_2 43 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 171 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 230 (accept_3_2 40 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 230
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 230 (accept_3_2 37 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 171 230 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 230 (accept_3_2 34 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 230 (accept_3_2 31 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 171 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 230 (accept_3_2 28 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 171 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 230
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 230 (accept_3_2 25 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 171 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 230 (accept_3_2 22 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 230
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 230 (accept_3_2 19 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 171 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 230 (accept_3_2 16 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 230 (Polychromatic418967fa.accept_17_15_1_9_1_10058 15 171 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 230 (accept_3_2 13 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 171 230 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 230 (accept_3_2 10 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 230
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 8 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 230 (accept_3_2 7 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  171 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 171 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 230 (accept_3_2 4 171 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 230 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 171 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 230 (accept_3_2 1 171 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 170 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 170 230 10 6 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 230 2 29 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 230 2 28 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 170 230 5 11 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 170 230 2 27 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 170 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 230 2 26 85 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 230 10 5 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 230 (accept_3_2 49 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 230 2 24 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 230 2 23 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 170 230 5 9 34 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 170 230 2 22 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 230 (accept_3_2 43 170 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 230 2 21 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 230
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 170 230 10 4 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 170 230 2 19 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 170 230 (accept_3_2 37 170 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 170 230 2 18 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 170 230 5 7 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 170 230 2 17 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 230 2 16 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 230 (accept_3_2 31 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 230 10 3 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 230 2 14 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 230
  (Polychromatic418967fa.accept_21_6_2_20_1_7803 27 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 230 2 13 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 170 230 5 5 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 170 230 2 12 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 170 230 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 170 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 230 2 11 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 230 10 2 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 230 (accept_3_2 19 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 230 2 9 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 230 2 8 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 170 230 5 3 34 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 170 230 2 7 85 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 230 (accept_3_2 13 170 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 230 2 6 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 230 10 1 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 170 230 (Polychromatic418967fa.accept_19_9_18_2_1_8383 9 170 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 230 2 4 85 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 230 (accept_3_2 7 170 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 230 2 3 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 170 230 5 1 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 170 230 2 2 85 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  170 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 230 2 1 85 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 230 (accept_3_2 1
  170 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 169 230 (Eq.refl Bool.true)
  (allA_of_3_0 62 169 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 168 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 168 230 2 31 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 168 230 (accept_3_2 61 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 230 2 30 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 230 (Polychromatic418967fa.accept_22_15_14_10_1_12219 59 168 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 230 2 29 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 230 2 28 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 230 (accept_3_2 55 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 230 2 27 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 230 2 26 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 230
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 168 230 2 25 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 168 230 (accept_3_2 49 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 230 2 24 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 230 2 23 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 230
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 45 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 230 2 22 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 230 (accept_3_2 43 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 230 2 21 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 230 (Polychromatic418967fa.accept_17_7_15_9_1_9019 41 168 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 230 2 20 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 230 2 19 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 230 (accept_3_2 37 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 230 2 18 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 230 2 17 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 230
  (Polychromatic418967fa.accept_19_14_16_2_1_6952 33 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 230 2 16 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 230 (accept_3_2 31 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 230 2 15 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 230 2 14 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 230
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 230 2 13 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 230 (accept_3_2 25 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 230 2 12 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 230 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 168 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 230 2 11 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 230 2 10 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 230 (accept_3_2 19 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 230 2 9 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 230 2 8 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 230
  (Polychromatic418967fa.accept_20_15_8_10_1_3602 15 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 230 2 7 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 230 (accept_3_2 13 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 230 2 6 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 230 2 5 84 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 230
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 230 2 4 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 230 (accept_3_2 7 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  230 2 3 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 230 (Polychromatic418967fa.accept_19_5_16_2_1_1717 5 168 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 230 2 2 84 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 230 2 1 84 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 230 (accept_3_2 1 168 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 167 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 230 (Polychromatic418967fa.accept_18_8_5_14_1_3353 62 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 230 (accept_3_2 61 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 230
  (Polychromatic418967fa.accept_13_8_11_9_1_593 60 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 167 230 (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 167 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 230 (accept_3_2 58 167 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 230 (accept_3_2 55 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 230 (accept_3_2 52 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 230
  (Polychromatic418967fa.accept_26_24_11_22_1_13751 50 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 167 230 (accept_3_2 49 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 167 230 (Polychromatic418967fa.accept_15_3_2_5_1_2980 48 167 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 230 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 230 (accept_3_2 46 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 230 (accept_3_2 43 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 230 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 230 (accept_3_2 40 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 230
  (Polychromatic418967fa.accept_17_4_14_9_1_5105 38 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 230 (accept_3_2 37 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 230 (Polychromatic418967fa.accept_19_17_15_2_1_6887 36 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 230 (Polychromatic418967fa.accept_14_7_13_6_1_1177 35 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 230 (accept_3_2 34 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 230 (accept_3_2 31 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 230 (Polychromatic418967fa.accept_19_11_15_2_1_4096 30 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 230 (accept_3_2 28 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 230
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 167 230 (accept_3_2 25 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 167 230 (Polychromatic418967fa.accept_22_2_13_10_1_13758 24 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 230 (accept_3_2 22 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 230 (accept_3_2 19 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 230 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 230 (accept_3_2 16 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 230 (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 230 (accept_3_2 13 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 230
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 230 (accept_3_2 10 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 230 (accept_3_2 7 167 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 230 (Polychromatic418967fa.accept_19_6_15_2_1_2857 6 167
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 230 (accept_3_2 4 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 230 (Polychromatic418967fa.accept_13_2_11_9_1_591 2 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 230 (accept_3_2 1 167 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  166 230 (Eq.refl Bool.true) (allA_of_3_0 65 166 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 165 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 165 230 5 13 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 165 230 (accept_3_2 64 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 230 (Polychromatic418967fa.accept_9_8_3_5_1_241
  62 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 230 (accept_3_2 61
  165 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 230 5 12 33 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 230 (accept_3_2 58 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 230 (Polychromatic418967fa.accept_20_17_5_10_1_3591 57 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 230 5 11 33 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 165 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 230 (accept_3_2 52 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 165 230 5 10 33 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 230 (accept_3_2 49 165 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 230 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 165
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 230 (accept_3_2 46 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  165 230 5 9 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 165 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 165 230 (accept_3_2 43 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 230 5 8 33 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 165 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 230 (accept_3_2 37 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 230 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 165 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 165 230 5 7 33 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 230 (accept_3_2 34 165 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 230 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 230
  (Polychromatic418967fa.accept_20_12_5_10_1_9540 32 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 230 (accept_3_2 31 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 165 230 5 6 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 165 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 230 (accept_3_2 28 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 230 (Polychromatic418967fa.accept_7_5_4_6_1_167
  26 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 230 5 5 33 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 165 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 230 (accept_3_2 22 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 230 (Polychromatic418967fa.accept_17_4_12_9_1_6379 21 165 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 230 5 4 33 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 230 (accept_3_2 19 165 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 230 (Polychromatic418967fa.accept_12_6_9_2_1_311
  18 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 230 (accept_3_2 16 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  165 230 5 3 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 165 230 (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 230 (accept_3_2 13 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 165 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 230 5 2 33 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 165 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 230 (accept_3_2 7 165 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 230 5 1 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 230 (accept_3_2 4 165 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 230 (accept_3_2 1 165 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 164 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 164 230 2 33 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 230 2 32 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 230
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 230 2 31 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 230 (accept_3_2 61 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 230 2 30 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 164 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 230 2 29 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 230 2 28 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 230 (accept_3_2 55 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 230 2 27 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 230 2 26 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 230 2 25 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 230 (accept_3_2 49 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 230 2 24 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 164 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 230 2 23 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 230
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 230 2 22 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 230 (accept_3_2 43 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 230 2 21 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 230 2 20 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 230 2 19 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 230 (accept_3_2 37 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 230 2 18 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 230 2 17 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 230 2 16 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 230 (accept_3_2 31 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 230 2 15 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 230 2 14 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 230
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 230 2 13 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 230 (accept_3_2 25 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 230 2 12 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 230 2 11 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 230 2 10 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 230 (accept_3_2 19 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 230 2 9 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 230 2 8 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 230 2 7 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 230 (accept_3_2 13 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 230 2 6 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 164 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 230 2 5 82 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 230 2 4 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 230 (accept_3_2 7 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  230 2 3 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 164 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 230 2 2 82 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 164 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 230 2 1 82 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 230 (accept_3_2 1 164 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 163 230 (Eq.refl Bool.true)
  (allA_of_3_0 68 163 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 162 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 162 230 2 34 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 230 (accept_3_2 67 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 230 2 33 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 162 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 230 2 32 81 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 230 2 31 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 230 (accept_3_2 61 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 230 2 30 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 230 (Polychromatic418967fa.accept_13_7_6_9_1_1831 59 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 230 2 29 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 230 2 28 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 230 (accept_3_2 55 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 230 2 27 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 230 2 26 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 230 2 25 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 230 (accept_3_2 49 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 230 2 24 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 162 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 230 2 23 81 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 230 2 22 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 230 (accept_3_2 43 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 230 2 21 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 230 2 20 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 230 2 19 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 230 (accept_3_2 37 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 230 2 18 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 230 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 230 2 17 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 230 2 16 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 230 (accept_3_2 31 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 230 2 15 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 230 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 230 2 14 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 230 2 13 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 230 (accept_3_2 25 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 230 2 12 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 162 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 230 2 11 81 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 230 2 10 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 230 (accept_3_2 19 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 230 2 9 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 230 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 230 2 8 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 230 2 7 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 230 (accept_3_2 13 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 230 2 6 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 230 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 230 2 5 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 230 2 4 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 230 (accept_3_2 7 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  230 2 3 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 230 2 2 81 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 162 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 230 2 1 81 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 230 (accept_3_2 1 162 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 161 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 161 230 23 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 161 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 230 (accept_3_2 67 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 161 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228
  65 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 230 (accept_3_2 64
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 161 230 (Polychromatic418967fa.accept_15_2_11_5_1_1266 62 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 230 (accept_3_2 61 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 161 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 230 (accept_3_2 58
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 230 (accept_3_2 55 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 161 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 230
  (Polychromatic418967fa.accept_13_1_5_9_1_226 53 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 161 230 (accept_3_2 52 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 161 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 230 (accept_3_2 49 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 161 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 161 230 23 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 161 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 161
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 230 (accept_3_2 43 161
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 161 230 (Polychromatic418967fa.accept_13_2_5_9_1_610 41 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 230 (accept_3_2 40 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228
  38 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 230 (accept_3_2 37
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 230
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 230 (accept_3_2 34 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 161 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 230 (Polychromatic418967fa.accept_12_8_5_2_1_746
  32 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 230 (accept_3_2 31
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 230 (accept_3_2 28 161 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 230 (Polychromatic418967fa.accept_19_7_9_2_1_4090
  26 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 230 (accept_3_2 25
  161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 23 161 230 23 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 161 230 (accept_3_2 22 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 230 (accept_3_2 19 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 230 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 230
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 230 (accept_3_2 16 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 230 (accept_3_2 13 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 230 (accept_3_2 10 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 230 (accept_3_2 7 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 230
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 230 (accept_3_2 4 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 230 (accept_3_2 1 161 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 160 230 (Eq.refl Bool.true) (allA_of_3_0 71 160 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 159 230 (Eq.refl Bool.true) (allA_succ_of_accept 71 159 230 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 230 (accept_3_2 70
  159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 159 230 (Polychromatic418967fa.accept_22_2_5_10_1_13757 68 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 230 (accept_3_2 67 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 230 (accept_3_2 64 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 159 230 (Polychromatic418967fa.accept_15_3_9_5_1_2082 63 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 159 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 230 (accept_3_2 61 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 230 (accept_3_2 58 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 230 (accept_3_2 55 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 230 (accept_3_2 52 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 230 (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 230 (accept_3_2 49 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 230 (accept_3_2 46 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 230 (accept_3_2 43 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 230 (accept_3_2 40 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 230 (accept_3_2 37 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 230 (accept_3_2 34 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 230 (accept_3_2 31 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 230 (accept_3_2 28 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 230 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 230 (accept_3_2 25 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 230 (Polychromatic418967fa.accept_19_5_7_2_1_1728 24 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 230 (accept_3_2 22 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 230 (accept_3_2 19 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 230 (accept_3_2 16 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 230 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 230 (accept_3_2 13 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 230 (accept_3_2 10 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 230 (accept_3_2 7 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 159 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 230 (accept_3_2 4 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 159 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 230 (accept_3_2 1 159 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 158 230 (Eq.refl Bool.true) (allA_succ_of_gcd 72 158 230 2 36 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 158 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 71 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 158 230 2 35 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 158 230 (Polychromatic418967fa.accept_19_12_6_2_1_5424 69 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 158 230 2 34 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 158 230 (accept_3_2 67 158 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 158 230 2 33 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 158 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 158 230 2 32 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 158 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 158 230 2 31 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 158 230 (accept_3_2 61 158 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 158 230 2 30 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 158 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 158 230 2 29 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 158 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 158 230 2 28 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 158 230 (accept_3_2 55 158 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 158 230 2 27 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 158 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 158 230 2 26 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 158 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 158 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 158 230 2 25 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 158 230 (accept_3_2 49 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 158 230 2 24 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 158 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 230 2 23 79 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 230 2 22 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 230 (accept_3_2 43 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 230 2 21 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 230 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 230 2 20 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 230
  (Polychromatic418967fa.accept_19_1_6_2_1_8341 39 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 230 2 19 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 230 (accept_3_2 37 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 230 2 18 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 230 (Polychromatic418967fa.accept_20_15_18_10_1_8067 35 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 230 2 17 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 230 2 16 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 230 (accept_3_2 31 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 230 2 15 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 230 (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 230 2 14 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 230 2 13 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 230 (accept_3_2 25 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 230 2 12 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 158 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 230 2 11 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 230
  (Polychromatic418967fa.accept_27_21_23_14_1_13756 21 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 158 230 2 10 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 158 230 (accept_3_2 19 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 230 2 9 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 158 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 230 2 8 79 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 230
  (Polychromatic418967fa.accept_19_15_6_2_1_6865 15 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 230 2 7 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 230 (accept_3_2 13 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 230 2 6 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 230 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 230 2 5 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 230 2 4 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 230 (accept_3_2 7 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  230 2 3 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 230 2 2 79 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 230 2 1 79 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 230 (accept_3_2 1 158 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 157 230 (Eq.refl
  Bool.true) (allA_of_3_0 74 157 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 156 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 156 230 2 37 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 230 (accept_3_2 73 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 230 2 36 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 230 2 35 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 230 2 34 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 230 (accept_3_2 67 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 230 2 33 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 230 2 32 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 230
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 63 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 156 230 2 31 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 156 230 (accept_3_2 61 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 230 2 30 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 230 2 29 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 230 2 28 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 230 (accept_3_2 55 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 230 2 27 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 230 2 26 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 230 2 25 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 230 (accept_3_2 49 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 230 2 24 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 230 2 23 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 230 2 22 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 230 (accept_3_2 43 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 230 2 21 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 156 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 230 2 20 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 230 2 19 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 230 (accept_3_2 37 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 230 2 18 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 230 2 17 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 230 2 16 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 230 (accept_3_2 31 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 230 2 15 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 230 2 14 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 230
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 230 2 13 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 230 (accept_3_2 25 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 230 2 12 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 230 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 156 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 230 2 11 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 230
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 21 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 156 230 2 10 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 156 230 (accept_3_2 19 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 230 2 9 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 230 2 8 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 230 2 7 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 230 (accept_3_2 13 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 230 2 6 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 230 2 5 78 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 230
  (Polychromatic418967fa.accept_19_9_4_2_1_9753 9 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 230 2 4 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 230 (accept_3_2 7 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  230 2 3 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 230 (Polychromatic418967fa.accept_19_5_4_2_1_6840 5 156 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 230 2 2 78 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 230 2 1 78 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 230 (accept_3_2 1 156 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 155 230 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 155 230 5 15 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 155 230 (Polychromatic418967fa.accept_18_2_11_14_1_69 74 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 230 (accept_3_2 73 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 155 230 5 14 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 155 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 230 (Polychromatic418967fa.accept_7_5_1_6_1_163
  68 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 230 (accept_3_2 67
  155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 155 230 5 13 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 155 230 (accept_3_2 64 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 155 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 230 (accept_3_2 61 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 155 230 5 12 31 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 155 230
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 59 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 155 230 (accept_3_2 58 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 230 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 155
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 155 230 5 11 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 155 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 230 (accept_3_2 52 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 155 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 155 230 5 10 31 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 155 230 (accept_3_2 49 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 230 (accept_3_2 46 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  155 230 5 9 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 155 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 155 230 (accept_3_2 43 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 155 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 230 5 8 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 230 (Polychromatic418967fa.accept_17_4_2_9_1_3896 38 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 230 (accept_3_2 37 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 230 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 230 5 7 31 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 230 (accept_3_2 34 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 230 (accept_3_2 31 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  155 230 5 6 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 230 (accept_3_2 28 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 155 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 230 5 5 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 230 (accept_3_2 22 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 230 5 4 31 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 230 (accept_3_2 19 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 230 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 155
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 230 (accept_3_2 16 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 230 5 3 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 230 (Polychromatic418967fa.accept_20_14_15_10_1_3554 14 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 230 (accept_3_2 13 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 230 (Polychromatic418967fa.accept_17_11_2_9_1_6358 11 155
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 230 5 2 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 230 (accept_3_2 7 155 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 155 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 230 5 1 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 230 (accept_3_2 4 155 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 230 (accept_3_2 1 155 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 154 230 (Eq.refl
  Bool.true) (allA_of_3_0 77 154 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 153 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 153 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 230 (accept_3_2 76 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 230
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 74 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 153 230 (accept_3_2 73 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 153 230 (Polychromatic418967fa.accept_19_15_1_2_1_6894 72 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 230 (accept_3_2 70 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077
  69 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 230
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 68 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 153 230 (accept_3_2 67 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 230 (accept_3_2 64 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 230
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 230 (accept_3_2 61 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 230 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 230 (accept_3_2 58 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 230 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 230
  (Polychromatic418967fa.accept_19_18_1_2_1_5430 56 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 230 (accept_3_2 55 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 230 (accept_3_2 52 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 230
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 50 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 230 (accept_3_2 49 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 230 (Polychromatic418967fa.accept_25_23_3_5_1_13755 48 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 230 (accept_3_2 46 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 230 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 230
  (Polychromatic418967fa.accept_19_6_1_2_1_12526 44 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 230 (accept_3_2 43 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 230 (accept_3_2 40 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 230
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 153 230 (accept_3_2 37 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 230 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 230 (accept_3_2 34 153 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 230
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 230 (Polychromatic418967fa.accept_13_6_10_9_1_4329 32 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 230 (accept_3_2 31 153 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 230 (accept_3_2 28 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 230 (accept_3_2 25 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 153
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 230 (accept_3_2 22 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 230 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 230 (Polychromatic418967fa.accept_22_20_21_10_1_13754 20 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 230 (accept_3_2 19 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 153
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 230 (accept_3_2 16 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 230 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 230 (accept_3_2 13 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 230 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 153
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 230 (accept_3_2 10 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 230 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 230 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 230 (accept_3_2 7 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 230 (accept_3_2 4 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 230 (Polychromatic418967fa.accept_15_2_3_5_1_2991 2 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 230 (accept_3_2 1 153 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 152 230 (Eq.refl Bool.true) (allA_succ_of_gcd 78 152 230 2 39 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 152 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 77 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 152 230 2 38 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 152 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 152 230 2 37 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 152 230 (accept_3_2 73 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 152 230 2 36 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 152 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 230 2 35 76 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 230 2 34 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 230 (accept_3_2 67 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 230 2 33 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 230 2 32 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 230
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 230 2 31 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 230 (accept_3_2 61 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 230 2 30 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 230 2 29 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 230 2 28 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 230 (accept_3_2 55 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 230 2 27 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 230 2 26 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 230 2 25 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 230 (accept_3_2 49 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 230 2 24 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 230 2 23 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 230
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 230 2 22 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 230 (accept_3_2 43 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 230 2 21 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 230 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 230 2 20 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 230 2 19 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 230 (accept_3_2 37 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 230 2 18 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 230 2 17 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 230 2 16 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 230 (accept_3_2 31 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 230 2 15 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 230 2 14 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 230
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 152 230 2 13 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 152 230 (accept_3_2 25 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 230 2 12 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 230 2 11 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 230 2 10 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 230 (accept_3_2 19 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 230 2 9 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 230 2 8 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 230 2 7 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 230 (accept_3_2 13 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 230 2 6 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 152 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 230 2 5 76 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 230
  (Polychromatic418967fa.accept_24_9_8_14_1_10466 9 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 230 2 4 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 230 (accept_3_2 7 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  230 2 3 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 152 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 230 2 2 76 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 152 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 230 2 1 76 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 230 (accept_3_2 1 152 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 151 230 (Eq.refl
  Bool.true) (allA_of_3_0 80 151 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 150 230 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 150 230 10 8 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 230 (accept_3_2 79 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 230 2 39 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 230 (Polychromatic418967fa.accept_22_11_18_10_1_12179 77 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 230 2 38 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 150 230 5 15 30 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 230 2 37 75 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 230
  (accept_3_2 73 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 230 2 36 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 230 10 7 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 230 2 34 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 230 (accept_3_2 67 150 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 230 2 33 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 230 5 13 30 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 150 230 2 32 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 230 2 31 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 230 (accept_3_2 61 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 230 10 6 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 230 (Polychromatic418967fa.accept_14_3_10_6_1_1136 59 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 230 2 29 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 230 2 28 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 150 230 5 11 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 230 2 27 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 150 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 230 2 26 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 230 10 5 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 230 (accept_3_2 49 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 230 2 24 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 150 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 230 2 23 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 230 5 9 30 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 230 2 22 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 230 (accept_3_2 43 150 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 230 2 21 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 230
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 230 10 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 150 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 230 2 19 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 230 (accept_3_2 37 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 230 2 18 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 230 5 7 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 230 2 17 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 230 2 16 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 230 (accept_3_2 31 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 230 10 3 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 150 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 230 2 14 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 230 2 13 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 150 230 5 5 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 150 230 2 12 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 230 2 11 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 230 10 2 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 230 (accept_3_2 19 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 230 2 9 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 230 2 8 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 230 5 3 30 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 230 2 7 75 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 230 (accept_3_2 13 150 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 230 2 6 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 230 10 1 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 230 2 4 75 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 230 (accept_3_2 7 150 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 230 2 3 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 230 5 1 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 230 2 2 75 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3
  150 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 230 2 1 75 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 230 (accept_3_2 1
  150 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 149 230 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 230 (accept_3_2 79
  149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 149 230 (Polychromatic418967fa.accept_15_2_14_5_1_2072 77 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 230 (accept_3_2 76 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 230 (Polychromatic418967fa.accept_7_4_2_6_1_337
  74 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 230 (accept_3_2 73
  149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 230
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 230 (accept_3_2 70 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 230 (Polychromatic418967fa.accept_12_8_5_2_1_746
  68 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 230 (accept_3_2 67
  149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 149 230 (Polychromatic418967fa.accept_16_1_5_6_1_4435 65 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 230 (accept_3_2 64 149 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 230
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 230 (accept_3_2 61 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 230 (accept_3_2 58 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 230 (accept_3_2 55 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 230 (accept_3_2 52 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 230 (accept_3_2 49 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 230 (Polychromatic418967fa.accept_21_6_2_20_1_7803 48 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 230 (accept_3_2 46 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 230 (accept_3_2 43 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 230 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 230 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 230 (accept_3_2 40 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 230 (accept_3_2 37 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 230 (accept_3_2 34 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 230 (accept_3_2 31 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 230 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 230 (accept_3_2 28 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 230
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 230 (accept_3_2 25 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 230 (accept_3_2 22 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 230 (accept_3_2 19 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 230 (accept_3_2 16 149 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 230
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 230 (accept_3_2 13 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 230 (Polychromatic418967fa.accept_25_12_24_5_1_13753 12 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 230 (accept_3_2 10 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 230 (accept_3_2 7 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 230 (Polychromatic418967fa.accept_15_6_14_5_1_2976 6 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 230 (accept_3_2 4 149 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 230
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 230 (accept_3_2 1 149 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 148 230 (Eq.refl
  Bool.true) (allA_of_3_0 83 148 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 147 230 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 230 (accept_3_2 82 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 230 (Polychromatic418967fa.accept_9_8_3_5_1_241
  80 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 230 (accept_3_2 79
  147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 78 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 230 (accept_3_2 76 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 147 230 (Polychromatic418967fa.accept_16_11_3_6_1_4462 75 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 147 230 (accept_3_2 73 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 147 230 (Polychromatic418967fa.accept_13_7_4_9_1_1865 72 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 230 (accept_3_2 70 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 230
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 68 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 230 (accept_3_2 67 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 147 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 230 (accept_3_2 64 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 230 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 147 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 230 (accept_3_2 61 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 230 (accept_3_2 58 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 230 (accept_3_2 55 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 230 (accept_3_2 52 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 230
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 230 (accept_3_2 49 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 147 230 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 230 (accept_3_2 46 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 230 (accept_3_2 43 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 230 (accept_3_2 40 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 230 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 147 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 230 (accept_3_2 37 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 230 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 230 (accept_3_2 34 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 230
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 230 (accept_3_2 31 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 230 (accept_3_2 28 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 230 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 230 (accept_3_2 25 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 230 (accept_3_2 22 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 230 (accept_3_2 19 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 230 (accept_3_2 16 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 230
  (Polychromatic418967fa.accept_22_14_15_10_1_12213 14 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 230 (accept_3_2 13 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 147 230 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 230 (accept_3_2 10
  147 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 230 (accept_3_2 7 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 230 (accept_3_2 4 147
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 230
  (Polychromatic418967fa.accept_17_3_11_9_1_5100 3 147 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 230 (accept_3_2 1 147 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 146 230 (Eq.refl Bool.true) (allA_succ_of_gcd 84 146 230 2 42 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 146 230
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 83 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 146 230 2 41 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 146 230 (Polychromatic418967fa.accept_15_6_11_5_1_168 81 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 146 230 2 40 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 146 230 (accept_3_2 79 146 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 146 230 2 39 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 146 230
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 77 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 146 230 2 38 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 146 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 146 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 146 230 2 37 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 146 230 (accept_3_2 73 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 146 230 2 36 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 146 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 71
  146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 230 2 35 73 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 230 2 34 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 230 (accept_3_2 67 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 230 2 33 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 230 (Polychromatic418967fa.accept_16_1_2_6_1_2295 65 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 230 2 32 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 230
  (Polychromatic418967fa.accept_19_6_13_2_1_8365 63 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 230 2 31 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 230 (accept_3_2 61 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 230 2 30 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 230 (Polychromatic418967fa.accept_13_7_3_9_1_1142 59 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 230 2 29 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 230 2 28 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 230 (accept_3_2 55 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 230 2 27 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 146 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 230 2 26 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 230 2 25 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 230 (accept_3_2 49 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 230 2 24 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 230 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 230 2 23 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 230
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 230 2 22 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 230 (accept_3_2 43 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 230 2 21 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 230 (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 230 2 20 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 230 2 19 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 230 (accept_3_2 37 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 230 2 18 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 146 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 230 2 17 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 230 2 16 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 230 (accept_3_2 31 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 230 2 15 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 230 2 14 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 230
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 230 2 13 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 230 (accept_3_2 25 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 230 2 12 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 230 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 230 2 11 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 230 2 10 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 230 (accept_3_2 19 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 230 2 9 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 146 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 230 2 8 73 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 230 2 7 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 230 (accept_3_2 13 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 230 2 6 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 230 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 230 2 5 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 230
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 230 2 4 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 230 (accept_3_2 7 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  230 2 3 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 230 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 146 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 230 2 2 73 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 146 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 230 2 1 73 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 230 (accept_3_2 1 146 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 145 230
  (Eq.refl Bool.true) (allA_of_3_0 86 145 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 144 230 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 144 230 2 43 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 144 230 (accept_3_2 85 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 230 2 42 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 83 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 230 2 41 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 230
  (Polychromatic418967fa.accept_20_1_4_10_1_3645 81 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 230 2 40 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 230 (accept_3_2 79 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 230 2 39 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 230 (Polychromatic418967fa.accept_21_14_18_20_1_12307 77 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 230 2 38 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 144 230 2 37 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 230 (accept_3_2 73 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 230 2 36 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 230 (Polychromatic418967fa.accept_13_6_1_9_1_619 71 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 230 2 35 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 230
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 69 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 230 2 34 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 230 (accept_3_2 67 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 230 2 33 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 230 2 32 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 230
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 63 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 230 2 31 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 230 (accept_3_2 61 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 230 2 30 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 230 2 29 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 230
  (Polychromatic418967fa.accept_11_2_1_10_1_196 57 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 230 2 28 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 230 (accept_3_2 55 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 230 2 27 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 230 (Polychromatic418967fa.accept_11_9_1_10_1_920 53 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 230 2 26 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 230 2 25 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 230 (accept_3_2 49 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 230 2 24 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 230 2 23 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 230 2 22 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 230 (accept_3_2 43 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 230 2 21 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 230 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 230 2 20 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 230
  (Polychromatic418967fa.accept_25_14_19_5_1_13752 39 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 144 230 2 19 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 144 230 (accept_3_2 37 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 230 2 18 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 230 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 230 2 17 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 230 2 16 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 230 (accept_3_2 31 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 230 2 15 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 230 (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 230 2 14 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 230
  (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 230 2 13 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 230 (accept_3_2 25 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 230 2 12 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 230 2 11 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 230
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 230 2 10 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 230 (accept_3_2 19 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 230 2 9 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 230 2 8 72 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 230
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 144 230 2 7 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 144 230 (accept_3_2 13 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 230 2 6 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 230 2 5 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 230 2 4 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 230 (accept_3_2 7 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  230 2 3 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 230 2 2 72 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 230 2 1 72 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 230 (accept_3_2 1 144 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 143 230
  (Eq.refl Bool.true) (allA_succ_of_accept 87 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 143 230 (accept_3_2 85 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 143 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 143 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 230 (accept_3_2 82 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 230 (accept_3_2 79 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 230 (accept_3_2 76 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 230 (accept_3_2 73 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 230 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 230 (accept_3_2 70 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 230 (accept_3_2 67 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 230 (accept_3_2 64 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 230
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 62 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 230 (accept_3_2 61 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 230 (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 230 (accept_3_2 58 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 230 (accept_3_2 55 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 230 (Polychromatic418967fa.accept_25_4_18_5_1_6529 54 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 230 (accept_3_2 52 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 230
  (Polychromatic418967fa.accept_19_12_10_2_1_12527 50 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 143 230 (accept_3_2 49 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 143 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 143 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 143 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 230 (accept_3_2 46 143 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 230 (accept_3_2 43 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 230 (accept_3_2 40 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 230 (accept_3_2 37 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 230 (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 230 (Polychromatic418967fa.accept_20_15_3_10_1_5066 35 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 230 (accept_3_2 34 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 230 (accept_3_2 31 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 230 (accept_3_2 28 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 230
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 230 (accept_3_2 25 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 230 (accept_3_2 22 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 230 (accept_3_2 19 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 230 (accept_3_2 16 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 230
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 230 (accept_3_2 13 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 230 (accept_3_2 10 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 230 (accept_3_2 7 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 230 (accept_3_2 4 143 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 230 (accept_3_2 1 143 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 142 230
  (Eq.refl Bool.true) (allA_of_3_0 89 142 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 141 230 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 230 (accept_3_2 88 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 230 (accept_3_2 85 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 141 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 230 (accept_3_2 82 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 230 (Polychromatic418967fa.accept_17_13_5_9_1_1762 81 141 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 141 230 (accept_3_2 79 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 141 230 (Polychromatic418967fa.accept_11_1_9_10_1_184 78 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 230 (accept_3_2 76 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 230 (accept_3_2 73 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 141 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 230 (accept_3_2 70 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 230 (Polychromatic418967fa.accept_20_9_1_10_1_6466 69 141 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 230 (accept_3_2 67 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 141 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 230 (accept_3_2 64 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 230 (accept_3_2 61 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 141 230 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 230 (accept_3_2 58 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 230 (accept_3_2 55 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 141 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 230 (accept_3_2 52 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 230
  (Polychromatic418967fa.accept_26_24_11_22_1_13751 50 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 141 230 (accept_3_2 49 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 141 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 141 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 230 (accept_3_2 46 141 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 230 (Polychromatic418967fa.accept_11_1_9_10_1_184
  45 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 230 (accept_3_2 43 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 230 (accept_3_2 40 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 230 (accept_3_2 37 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 230 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 230 (accept_3_2 34 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 230
  (Polychromatic418967fa.accept_19_13_8_2_1_4089 32 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 230 (accept_3_2 31 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 230 (accept_3_2 28 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 230 (accept_3_2 25 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 230 (Polychromatic418967fa.accept_17_7_5_9_1_7763 24 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 230 (accept_3_2 22 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 230
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 230 (accept_3_2 19 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 230 (accept_3_2 16 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 230
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 230 (accept_3_2 13 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 230 (accept_3_2 10 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 230
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 230 (accept_3_2 7 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 230 (accept_3_2 4 141 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 230 (accept_3_2 1 141 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 140 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 140 230 10 9 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 140 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 140 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 230 2 44 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 230
  (Polychromatic418967fa.accept_17_2_4_9_1_2791 87 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 230 2 43 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 140 230 5 17 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 140 230 2 42 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 140 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 140
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 230 2 41 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 230
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 81 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 230 10 8 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 230 (accept_3_2 79 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 230 2 39 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 140 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 230 2 38 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 140 230 5 15 28 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 140 230 2 37 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 140 230 (accept_3_2 73
  140 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 140 230 2 36 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 140 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 140 230 10 7 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 140 230 (Polychromatic418967fa.accept_21_6_14_20_1_4594 69 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 140 230 2 34 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 140 230 (accept_3_2 67 140 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 140 230 2 33 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 140 230 5 13 28 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 140 230 2 32 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 230
  (Polychromatic418967fa.accept_17_12_4_9_1_3889 63 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 230 2 31 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 230 (accept_3_2 61 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 230 10 6 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 230 2 29 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 230
  (Polychromatic418967fa.accept_21_15_14_20_1_13750 57 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 140 230 2 28 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 140 230 5 11 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 140 230 2 27 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 230 (Polychromatic418967fa.accept_11_9_8_10_1_934
  53 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 230 2 26 70 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 230
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 140 230 10 5 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 140 230 (accept_3_2 49 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 230 2 24 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 230 2 23 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 140 230 5 9 28 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 140 230 2 22 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 140 230 (accept_3_2 43
  140 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 140 230 2 21 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140 230
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 140 230 10 4 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 140 230 (Polychromatic418967fa.accept_19_1_7_2_1_4106 39 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 230 2 19 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 230 (accept_3_2 37 140 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 230 2 18 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 140 230 5 7 28 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 140 230 2 17 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 230
  (Polychromatic418967fa.accept_19_14_7_2_1_11116 33 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 140 230 2 16 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 140 230 (accept_3_2 31 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 230 10 3 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 140 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 230 2 14 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 230
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 230 2 13 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 140 230 5 5 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 140 230 2 12 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 140 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 230 2 11 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 230
  (Polychromatic418967fa.accept_25_21_15_5_1_13749 21 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 140 230 10 2 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 140 230 (accept_3_2 19 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 230 2 9 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 230 2 8 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 230 5 3 28 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 230 2 7 70 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 230 (accept_3_2 13 140 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 230 2 6 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 230
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 230 10 1 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 140 230 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 140 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 230 2 4 70 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 230 (accept_3_2 7 140 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 230 2 3 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140 230 5 1 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140 230 2 2 70 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 230 (Polychromatic418967fa.accept_27_3_5_14_1_13748
  3 140 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 230 2 1 70 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 230 (accept_3_2 1
  140 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 139 230
  (Eq.refl Bool.true) (allA_of_3_0 92 139 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 138 230 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 138 230 46 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 230 (accept_3_2 91 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 230 2 45 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 230 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 230 2 44 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 230 2 43 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 230 (accept_3_2 85 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 230 2 42 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 230 2 41 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 230 2 40 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 230 (accept_3_2 79 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 230 2 39 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 230 (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 230 2 38 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 230 2 37 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 230 (accept_3_2 73 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 230 2 36 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 230 2 35 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 138 230 23 3 6 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 138 230 2 34 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 230 (accept_3_2 67 138 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 138 230 2 33 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 138 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 230 2 32 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 230 2 31 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 230 (accept_3_2 61 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 138 230 2 30 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 138 230 (Polychromatic418967fa.accept_13_7_8_9_1_1158
  59 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 230 2 29 69 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 230 2 28 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 230 (accept_3_2 55 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 230 2 27 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 230 2 26 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 230
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 230 2 25 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 230 (accept_3_2 49 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 230 2 24 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 230 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 230 46 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273
  45 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 230 2 22 69 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 230
  (accept_3_2 43 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 230 2 21 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 230
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 138 230 2 20 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 138 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 230 2 19 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 230 (accept_3_2 37 138 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 138 230 2 18 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 138 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 230 2 17 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 230 2 16 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 230 (accept_3_2 31 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 230 2 15 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 230 2 14 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 230
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 230 2 13 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 230 (accept_3_2 25 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 230 2 12 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 23 138 230 23 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 138 230 2 11 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 138 230 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 230 2 10 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 230 (accept_3_2 19 138 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 138 230 2 9 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 138 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 230 2 8 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 230 2 7 69 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 230 (accept_3_2 13 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 230 2 6 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 230 2 5 69 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 230 2 4 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 230 (accept_3_2 7 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  230 2 3 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 230 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 138 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 230 2 2 69 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 138 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 230 2 1 69 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 230 (accept_3_2 1 138 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 137
  230 (Eq.refl Bool.true) (allA_succ_of_accept 93 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 92 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 137 230 (accept_3_2 91 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 137 230 (Polychromatic418967fa.accept_19_14_4_2_1_2840 90 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 137 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 230 (accept_3_2 88 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 230 (accept_3_2 85 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 230 (accept_3_2 82 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 80 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 230 (accept_3_2 79 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 230 (Polychromatic418967fa.accept_16_13_9_6_1_2306 77 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 230 (accept_3_2 76 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 137 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 230
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 74 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 230 (accept_3_2 73 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 230 (accept_3_2 70 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 230 (accept_3_2 67 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 230 (accept_3_2 64 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 230 (accept_3_2 61 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 230 (accept_3_2 58 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 230 (accept_3_2 55 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 230 (accept_3_2 52 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 230
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 230 (accept_3_2 49 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 230 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 230 (accept_3_2 46 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 230 (accept_3_2 43 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 230 (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 230 (accept_3_2 40 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 230
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 230 (accept_3_2 37 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 230 (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 230 (accept_3_2 34 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 230 (accept_3_2 31 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 230 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 230 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 230 (accept_3_2 28 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 230
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 230 (accept_3_2 25 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 230 (accept_3_2 22 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 230
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 230 (accept_3_2 19 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 230 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 230 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 230 (accept_3_2 16 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 230
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 230 (accept_3_2 13 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 230 (accept_3_2 10 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 230
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 230 (accept_3_2 7 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 230 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 230 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 230 (accept_3_2 4 137 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 230
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 230 (accept_3_2 1 137 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 136
  230 (Eq.refl Bool.true) (allA_of_3_0 95 136 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 135 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 95 135 230 5 19 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 135 230 (accept_3_2 94 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 92
  135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 230 (accept_3_2 91
  135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 135 230 5 18 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 135 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 230 (accept_3_2 88 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 230 (Polychromatic418967fa.accept_20_6_15_10_1_3555 86 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 135 230 5 17 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 135 230
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 84 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 230 (accept_3_2 82 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 135 230 5 16 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 230 (accept_3_2 79 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 135 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 230 (accept_3_2 76 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  135 230 5 15 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 135 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 230 (accept_3_2 73 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 230 (Polychromatic418967fa.accept_20_12_15_10_1_6520 72 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 135 230 5 14 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 230 (Polychromatic418967fa.accept_13_3_5_9_1_5285
  68 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 230 (accept_3_2 67
  135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 135 230 5 13 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 135 230 (accept_3_2 64 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 135 230 (Polychromatic418967fa.accept_16_15_7_6_1_1453 63 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 62 135
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 230 (accept_3_2 61 135
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 230 5 12 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 230
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 230 (accept_3_2 58 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 230 (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 135 230 5 11 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 135 230
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 230 (accept_3_2 52 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 230 (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 135 230 5 10 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 135 230 (accept_3_2 49 135 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 230
  (Polychromatic418967fa.accept_20_8_15_10_1_8045 48 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 230 (accept_3_2 46 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 230 5 9 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 230 (Polychromatic418967fa.accept_17_10_16_9_1_5127 44 135
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 230 (accept_3_2 43 135
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 230
  (Polychromatic418967fa.accept_12_6_3_2_1_743 42 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 230 5 8 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 135 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 230 (accept_3_2 37 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 135 230 5 7 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 135 230 (accept_3_2 34 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 135 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 230 (accept_3_2 31 135 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 230 5 6 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 230 (accept_3_2 28 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 230 (Polychromatic418967fa.accept_20_6_15_10_1_3555 26 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 230 5 5 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 135 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 230 (accept_3_2 22 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 230 5 4 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 230 (accept_3_2 19 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 230 (accept_3_2 16 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  135 230 5 3 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 135 230 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 135 230 (accept_3_2 13 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 135 230 (Polychromatic418967fa.accept_20_12_15_10_1_6520 12 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 230 5 2 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 230 (accept_3_2 7 135 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 230 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 230 5 1 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 230 (accept_3_2 4 135 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 230
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 230 (accept_3_2 1 135 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 134
  230 (Eq.refl Bool.true) (allA_succ_of_gcd 96 134 230 2 48 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 134 230 (Polychromatic418967fa.accept_18_5_8_14_1_1282 95 134
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 230 2 47 67 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 230 2 46 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 230 (accept_3_2 91 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 230 2 45 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 230 2 44 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 230 2 43 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 230 (accept_3_2 85 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 230 2 42 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 230 2 41 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 230
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 81 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 230 2 40 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 230 (accept_3_2 79 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 230 2 39 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 230 (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 230 2 38 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 230 2 37 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 230 (accept_3_2 73 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 230 2 36 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 230 (Polychromatic418967fa.accept_13_6_4_9_1_4326 71 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 230 2 35 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 230 2 34 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 230 (accept_3_2 67 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 230 2 33 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 230 2 32 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 230
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 230 2 31 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 230 (accept_3_2 61 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 230 2 30 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 230 (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 230 2 29 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 230 2 28 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 230 (accept_3_2 55 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 230 2 27 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 230 (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 230 2 26 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 230 2 25 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 230 (accept_3_2 49 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 230 2 24 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 230 2 23 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 230
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 230 2 22 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 230 (accept_3_2 43 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 230 2 21 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 230 (Polychromatic418967fa.accept_17_7_15_9_1_9019 41 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 230 2 20 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 230 2 19 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 230 (accept_3_2 37 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 230 2 18 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 230 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 230 2 17 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 230
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 230 2 16 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 230 (accept_3_2 31 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 230 2 15 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 230 2 14 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 230
  (Polychromatic418967fa.accept_19_8_1_2_1_13747 27 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 230 2 13 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 230 (accept_3_2 25 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 230 2 12 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 230 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 230 2 11 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 230 2 10 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 230 (accept_3_2 19 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 230 2 9 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 230 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 230 2 8 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 230 2 7 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 230 (accept_3_2 13 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 230 2 6 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 230 2 5 67 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 230
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 230 2 4 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 230 (accept_3_2 7 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  230 2 3 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 230 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 230 2 2 67 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 134 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 230 2 1 67 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 230 (accept_3_2 1 134 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  133 230 (Eq.refl Bool.true) (allA_of_3_0 98 133 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 132 230
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 230 2 49 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 230 (accept_3_2 97 132 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 132 230 2 48 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 132 230 (Polychromatic418967fa.accept_17_10_13_9_1_3913 95 132 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 132 230 2 47 66 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 132 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 132 230 2 46 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 132 230 (accept_3_2 91 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 230 2 45 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 230 2 44 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 230
  (Polychromatic418967fa.accept_21_3_6_20_1_9278 87 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 230 2 43 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 230 (accept_3_2 85 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 230 2 42 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 230 2 41 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 230
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 230 2 40 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 230 (accept_3_2 79 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 230 2 39 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 230 (Polychromatic418967fa.accept_15_2_12_5_1_2107 77 132 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 230 2 38 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 230 2 37 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 230 (accept_3_2 73 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 230 2 36 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 230 2 35 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 230
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 69 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 230 2 34 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 230 (accept_3_2 67 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 230 2 33 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 230 2 32 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 230
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 132 230 2 31 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 132 230 (accept_3_2 61 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 230 2 30 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 230 (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 132 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 230 2 29 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 230 2 28 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 230 (accept_3_2 55 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 230 2 27 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 230 2 26 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 230
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 230 2 25 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 230 (accept_3_2 49 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 230 2 24 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 230 2 23 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 230
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 230 2 22 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 230 (accept_3_2 43 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 230 2 21 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 230 (Polychromatic418967fa.accept_19_3_18_2_1_6935 41 132 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 230 2 20 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 230 2 19 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 230 (accept_3_2 37 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 230 2 18 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 230 2 17 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 230
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 132 230 2 16 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 132 230 (accept_3_2 31 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 230 2 15 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 230 2 14 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 230
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 230 2 13 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 230 (accept_3_2 25 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 230 2 12 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 230 (Polychromatic418967fa.accept_15_8_12_5_1_2987 23 132 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 230 2 11 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 230
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 230 2 10 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 230 (accept_3_2 19 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 230 2 9 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 230 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 230 2 8 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 230
  (Polychromatic418967fa.accept_19_15_18_2_1_6857 15 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 230 2 7 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 230 (accept_3_2 13 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 230 2 6 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 230 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 132 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 230 2 5 66 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 230
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 230 2 4 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 230 (accept_3_2 7 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  230 2 3 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 230 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 132 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 230 2 2 66 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 230 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 132 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 230 2 1 66 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 230 (accept_3_2 1 132 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  131 230 (Eq.refl Bool.true) (allA_succ_of_accept 99 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 230
  (Polychromatic418967fa.accept_15_8_11_5_1_169 98 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 230 (accept_3_2 97 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 96 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 230 (accept_3_2 94 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 92 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 230 (accept_3_2 91 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 230 (Polychromatic418967fa.accept_17_5_12_9_1_10091 90 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 230 (accept_3_2 88 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 230
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 86 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 230 (accept_3_2 85 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 230 (Polychromatic418967fa.accept_13_6_1_9_1_619 84 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 230 (Polychromatic418967fa.accept_13_5_1_9_1_618 83 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 230 (accept_3_2 82 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 230 (accept_3_2 79 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 230 (accept_3_2 76 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 230 (accept_3_2 73 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 230 (Polychromatic418967fa.accept_17_4_12_9_1_6379 72 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 230 (accept_3_2 70 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 230 (accept_3_2 67 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 230 (Polychromatic418967fa.accept_15_6_11_5_1_168 66 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 230 (accept_3_2 64 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 230
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 62 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 230 (accept_3_2 61 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 230 (Polychromatic418967fa.accept_16_11_3_6_1_4462 59 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 230 (accept_3_2 58 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 230 (accept_3_2 55 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 230 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 230 (accept_3_2 52 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 230
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 230 (accept_3_2 49 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 230 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 230 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 230 (accept_3_2 46 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 230 (accept_3_2 43 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 230 (Polychromatic418967fa.accept_19_4_17_2_1_5409 42 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 230 (accept_3_2 40 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 230
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 230 (accept_3_2 37 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 230 (Polychromatic418967fa.accept_19_16_17_2_1_6856 35 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 230 (accept_3_2 34 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 230
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 230 (accept_3_2 31 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 230 (Polychromatic418967fa.accept_26_4_1_22_1_13746 30 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 230 (accept_3_2 28 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 230
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 230 (accept_3_2 25 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 230 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 230 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 230 (accept_3_2 22 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 230
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 230 (accept_3_2 19 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 230 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 230 (accept_3_2 16 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 230
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 230 (accept_3_2 13 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 230 (Polychromatic418967fa.accept_19_12_17_2_1_6888 12 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 230 (Polychromatic418967fa.accept_7_4_5_6_1_344
  11 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 230 (accept_3_2 10
  131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 230
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 131 230 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 230 (accept_3_2 7 131 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 131 230 (Polychromatic418967fa.accept_13_6_1_9_1_619 6 131 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 230 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 230 (accept_3_2 4 131
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 230 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 230
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 230 (accept_3_2 1 131 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 130 230 (Eq.refl Bool.true) (allA_of_3_0 101 130 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 129
  230 (Eq.refl Bool.true) (allA_succ_of_accept 101 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 230 (accept_3_2 100 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 99
  129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 98 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 230 (accept_3_2 97 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 230 (accept_3_2 94 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 230 (accept_3_2 91 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 129 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 230 (accept_3_2 88 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 230 (accept_3_2 85 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 230 (Polychromatic418967fa.accept_17_16_10_9_1_11361 84 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 230 (accept_3_2 82 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 230 (accept_3_2 79 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 230 (accept_3_2 76 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 230 (accept_3_2 73 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 230 (accept_3_2 70 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 230
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 68 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 230 (accept_3_2 67 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 230 (accept_3_2 64 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 230 (accept_3_2 61 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 230 (accept_3_2 58 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 230 (Polychromatic418967fa.accept_15_12_9_5_1_2973 57 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 230 (accept_3_2 55 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 230 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 230 (accept_3_2 52 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 230
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 230 (accept_3_2 49 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 230 (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 230 (accept_3_2 46 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 230 (Polychromatic418967fa.accept_18_9_3_14_1_3361 45 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 230 (accept_3_2 43 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 230 (accept_3_2 40 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 230 (accept_3_2 37 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 230 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 230 (accept_3_2 34 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 230
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 230 (accept_3_2 31 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 230 (accept_3_2 28 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 230 (accept_3_2 25 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 230 (accept_3_2 22 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 230 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 129 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 230
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 230 (accept_3_2 19 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 230 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 230 (accept_3_2 16 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 230
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 230 (accept_3_2 13 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 230 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 230 (accept_3_2 10 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 230 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 230
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 230 (accept_3_2 7 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 230 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 230 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 230 (accept_3_2 4 129 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 230
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 230 (accept_3_2 1 129 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 128 230 (Eq.refl Bool.true) (allA_succ_of_gcd 102 128 230 2 51 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 128 230 (Polychromatic418967fa.accept_7_3_2_6_1_56
  101 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 230 2 50 64 115
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 230 2 49 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 230 (accept_3_2 97 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 230 2 48 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 128 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 230 2 47 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 230 2 46 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 230 (accept_3_2 91 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 230 2 45 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 230 2 44 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 230 2 43 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 230 (accept_3_2 85 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 230 2 42 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 128 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 230 2 41 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 230 2 40 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 230 (accept_3_2 79 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 230 2 39 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 230 2 38 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 230 2 37 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 230 (accept_3_2 73 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 230 2 36 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 230 2 35 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 230 2 34 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 230 (accept_3_2 67 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 230 2 33 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 230 2 32 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 230
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 230 2 31 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 230 (accept_3_2 61 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 230 2 30 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 230 2 29 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 230 2 28 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 230 (accept_3_2 55 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 230 2 27 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 230 2 26 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 230 2 25 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 230 (accept_3_2 49 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 230 2 24 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 230 (Polychromatic418967fa.accept_11_3_7_10_1_180 47 128 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 230 2 23 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 230
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 230 2 22 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 230 (accept_3_2 43 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 230 2 21 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 230 2 20 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 230
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 230 2 19 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 230 (accept_3_2 37 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 230 2 18 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 230 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 230 2 17 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 230
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 230 2 16 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 230 (accept_3_2 31 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 230 2 15 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 230 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 230 2 14 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 230
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 230 2 13 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 230 (accept_3_2 25 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 230 2 12 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 230 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 128 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 230 2 11 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 230
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 230 2 10 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 230 (accept_3_2 19 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 230 2 9 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 230 2 8 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 230
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 230 2 7 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 230 (accept_3_2 13 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 230 2 6 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 230 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 230 2 5 64 115 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 230
  (Polychromatic418967fa.accept_21_9_2_20_1_857 9 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 230 2 4 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 230 (accept_3_2 7 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  230 2 3 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 230 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 128 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 230 2 2 64 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 128 230 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 128 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 230 2 1 64 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 230 (accept_3_2 1 128 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 127 230 (Eq.refl Bool.true) (allA_of_3_0 104 127 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 126
  230 (Eq.refl Bool.true) (allA_succ_of_gcd 104 126 230 2 52 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 230 (accept_3_2 103 126 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 230 2 51 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 101 126 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 230 2 50 63 115 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 99 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 230 2 49 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 230 (accept_3_2 97 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 230 2 48 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 230 (Polychromatic418967fa.accept_20_15_6_10_1_9569 95 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 230 2 47 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 93 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 230 2 46 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 230 (accept_3_2 91 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 230 2 45 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 230 (Polychromatic418967fa.accept_15_14_6_5_1_7215 89 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 230 2 44 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 230 2 43 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 230 (accept_3_2 85 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 230 2 42 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 83 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 230 2 41 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 81 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 230 2 40 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 230 (accept_3_2 79 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 230 2 39 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 230 (Polychromatic418967fa.accept_19_1_12_2_1_6918 77 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 230 2 38 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 230 2 37 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 230 (accept_3_2 73 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 230 2 36 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 230 2 35 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 230 2 34 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 230 (accept_3_2 67 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 230 2 33 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 230 (Polychromatic418967fa.accept_20_5_6_10_1_3536 65 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 230 2 32 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 230 2 31 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 230 (accept_3_2 61 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 230 2 30 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 230 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 230 2 29 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 230 2 28 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 230 (accept_3_2 55 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 230 2 27 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 230 (Polychromatic418967fa.accept_17_2_7_9_1_2796 53 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 230 2 26 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 230 2 25 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 230 (accept_3_2 49 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 230 2 24 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 230 (Polychromatic418967fa.accept_19_9_12_2_1_9776 47 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 230 2 23 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 230 2 22 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 230 (accept_3_2 43 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 230 2 21 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 230 2 20 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 230
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 230 2 19 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 230 (accept_3_2 37 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 230 2 18 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 230 (Polychromatic418967fa.accept_20_15_6_10_1_9569 35 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 230 2 17 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 230 2 16 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 230 (accept_3_2 31 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 230 2 15 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 230 (Polychromatic418967fa.accept_15_14_6_5_1_7215 29 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 230 2 14 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 230
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 230 2 13 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 230 (accept_3_2 25 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 230 2 12 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 230 (Polychromatic418967fa.accept_19_4_12_2_1_11158 23 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 230 2 11 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 230 2 10 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 230 (accept_3_2 19 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 230 2 9 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 230 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 230 2 8 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 230
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 230 2 7 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 230 (accept_3_2 13 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 230 2 6 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 230 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 230 2 5 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 230
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 230 2 4 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 230 (accept_3_2 7 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  230 2 3 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 230 (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 126 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 230 2 2 63 115 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 230 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 230 2 1 63 115 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 230 (accept_3_2 1 126 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  230)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 125 230 (Eq.refl Bool.true) (allA_succ_of_gcd 105 125 230 5 21 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 125 230
  (Polychromatic418967fa.accept_11_5_4_10_1_524 104 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 125 230 (accept_3_2 103 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 125 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 125 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 125 230 5 20 25 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 125 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 230 (Polychromatic418967fa.accept_13_7_8_9_1_1158 98 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 230 (accept_3_2 97 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 125 230 5 19 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 125 230 (accept_3_2 94 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 125 230 (accept_3_2 91 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  125 230 5 18 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 125 230 (Polychromatic418967fa.accept_13_11_8_9_1_1161 89 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 230 (accept_3_2 88 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 230
  (Polychromatic418967fa.accept_19_10_11_2_1_8354 86 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 85 125 230 5 17 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 84 125 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 230 (accept_3_2 82 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 125 230 5 16 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 125 230 (accept_3_2 79 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 125 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 230 (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 125
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 230 (accept_3_2 76 125
  230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 125 230 5 15 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 125 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 230 (accept_3_2 73 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 230 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 125 230 5 14 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 125 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 125 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 230 (accept_3_2 67 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 125 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 125 230 5 13 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 125 230 (accept_3_2 64 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 230
  (Polychromatic418967fa.accept_20_2_5_10_1_3535 62 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 230 (accept_3_2 61 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  125 230 5 12 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 230 (accept_3_2 58 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 125 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 230 (Polychromatic418967fa.accept_9_2_8_5_1_228
  56 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 125 230 5 11 25 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 125 230
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 230 (accept_3_2 52 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 125 230 5 10 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 125 230 (accept_3_2 49
  125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 230
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 230 (accept_3_2 46 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 125 230 5 9 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 125 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 230 (accept_3_2 43 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 230
  (Polychromatic418967fa.accept_16_9_13_6_1_2334 41 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 125 230 5 8 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 230 (accept_3_2 37 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 230
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 125 230 5 7 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 125 230 (accept_3_2 34 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 230 (accept_3_2 31 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 125 230 5 6 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 125 230 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 230 (accept_3_2 28
  125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 230
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 125 230 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 230 5 5 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 230
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 230 (accept_3_2 22 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 230 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 230 5 4 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 230 (accept_3_2 19 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 230 (Polychromatic418967fa.accept_20_18_5_10_1_3533 18 125
  230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 230
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 230 (accept_3_2 16 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  125 230 5 3 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 125 230 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 230 (accept_3_2 13 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 230 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 230
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 230 5 2 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 230
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 230 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 230 (accept_3_2 7 125 230 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 230 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 230 5 1 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 230 (accept_3_2 4 125 230 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 230 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 230 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 230
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 230 (accept_3_2 1 125 230 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  230))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_230_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


