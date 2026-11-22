-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch226
-- name    : Polychromatic418967fa_Branch226
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:25:38.323372+00:00
-- url     : https://prove2.me/theorems/d3e90d54-d4ca-417b-9b2b-ae26119265f9
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch226_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_226 : allB 226 226 :=
  allB_succ' 2 225 226 (Eq.refl Bool.true) (allA_succ_of_accept 1 225 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  225 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 226)) (allB_succ' 3 224 226
  (Eq.refl Bool.true) (allA_of_3_1 3 224 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 223 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 223 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 226 (accept_3_3 2 223 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 226)))) (allB_succ' 5 222 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 222 226 2 2 111 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 222 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 226 2 1 111 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 226
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 222 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 226))))) (allB_succ' 6 221 226 (Eq.refl Bool.true) (allA_of_3_1 6 221 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 7 220 226 (Eq.refl Bool.true) (allA_succ_of_gcd 6 220 226 2 3 110 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 226 (accept_3_3 5 220 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 226 2 2 110 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 220 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 226 2 1 110 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 220 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 226))))))) (allB_succ' 8 219 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 219 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 219 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 219 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 226 (accept_3_3 5 219 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  219 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 226
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 219 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 226 (accept_3_3 2 219 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 226)))))))) (allB_succ' 9 218 226 (Eq.refl Bool.true) (allA_of_3_1 9 218 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 217 226 (Eq.refl Bool.true) (allA_succ_of_accept 9 217 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 226 (accept_3_3 8 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 226 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 217 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 226 (accept_3_3 5 217 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 217 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 226 (accept_3_3 2 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 226 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 217 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 226)))))))))) (allB_succ' 11 216 226 (Eq.refl Bool.true) (allA_succ_of_gcd 10 216 226 2 5
  108 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 226
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 216 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 226 2 4 108 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 216 226 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 216 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 226 2 3 108 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 226 (accept_3_3 5 216 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 226 2 2 108 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  216 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 226 2 1 108 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 216 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 226))))))))))) (allB_succ' 12 215 226 (Eq.refl Bool.true) (allA_of_3_1 12 215 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 214 226 (Eq.refl Bool.true) (allA_succ_of_gcd 12 214 226 2 6 107 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 214 226 (accept_3_3 11
  214 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 214 226 2 5 107 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 214 226
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 214 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 214 226 2 4 107 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 214 226 (Polychromatic418967fa.accept_19_7_5_17_1_3849 7 214 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 214 226 2 3 107 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 214 226 (accept_3_3 5 214 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 214 226 2 2 107 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 214 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  214 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 226 2 1 107 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 226
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 214 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 226))))))))))))) (allB_succ' 14 213 226 (Eq.refl Bool.true) (allA_succ_of_accept 13 213 226
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 213 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 213 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 226 (accept_3_3 11 213 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 213 226 (Polychromatic418967fa.accept_19_10_4_17_1_1544 10 213 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 226
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 226 (accept_3_3 8 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 213 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 226 (accept_3_3 5 213 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 213 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 226 (accept_3_3 2 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 226)))))))))))))) (allB_succ' 15 212 226 (Eq.refl Bool.true) (allA_of_3_1 15 212 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 211 226 (Eq.refl Bool.true) (allA_succ_of_accept 15 211 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 226 (accept_3_3 14 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 211 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 226 (accept_3_3 11 211 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 211 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 226 (accept_3_3 8 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 211 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 226 (accept_3_3 5 211 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 226 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 211 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 226 (accept_3_3 2 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 226)))))))))))))))) (allB_succ' 17 210 226 (Eq.refl Bool.true) (allA_succ_of_gcd 16 210 226
  2 8 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  210 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 210 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 210 226 2 7 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 210 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 210 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 226 2 6 105 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 226 (accept_3_3 11 210 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 226 2 5 105 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 226
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 210 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 226 2 4 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 210 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 226 2 3 105 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 226 (accept_3_3 5 210 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 226 2 2 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  210 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 226 2 1 105 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 226
  (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 210 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 226))))))))))))))))) (allB_succ' 18 209 226 (Eq.refl Bool.true) (allA_of_3_1 18 209 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 208 226 (Eq.refl Bool.true) (allA_succ_of_gcd 18 208 226 2 9 104 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 208 226
  (accept_3_3 17 208 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 208 226 2 8 104 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 208 226
  (Polychromatic418967fa.accept_22_15_10_6_1_7097 15 208 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 208 226 2 7 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 208 226 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 208 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 208 226 2 6 104 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 226 (accept_3_3 11 208 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 226 2 5 104 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 226
  (Polychromatic418967fa.accept_25_9_8_1_1_13523 9 208 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 226 2 4 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 208 226 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 208 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 226 2 3 104 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 226 (accept_3_3 5 208 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 226 2 2 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  208 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 226 2 1 104 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 208 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 226))))))))))))))))))) (allB_succ' 20 207 226 (Eq.refl Bool.true) (allA_succ_of_accept 19 207 226
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 207 226 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 207 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 226 (accept_3_3 17 207 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 226 (Polychromatic418967fa.accept_20_16_7_6_1_7815 16 207 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 226
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 226 (accept_3_3 14 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 207 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 207 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 226 (accept_3_3 11 207 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 226 (Polychromatic418967fa.accept_25_10_7_1_1_13522 10 207 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 226 (accept_3_3 8 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 207 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 226 (accept_3_3 5 207 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 226 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 207 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 226
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 226 (accept_3_3 2 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 226)))))))))))))))))))) (allB_succ' 21 206 226 (Eq.refl Bool.true) (allA_of_3_1 21 206 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 205 226 (Eq.refl Bool.true) (allA_succ_of_accept 21 205 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 226 (accept_3_3 20 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 226 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 226 (accept_3_3 17 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 205 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 226 (accept_3_3 14 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 226 (accept_3_3 11 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 226 (Polychromatic418967fa.accept_19_10_15_17_1_6590 10 205 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 226 (accept_3_3 8 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 226 (accept_3_3 5 205 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 205 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 226 (accept_3_3 2 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 226 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 205 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 226)))))))))))))))))))))) (allB_succ' 23 204 226 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  204 226 2 11 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 204 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 226 2 10 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 226
  (Polychromatic418967fa.accept_25_19_4_1_1_13521 19 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 204 226 2 9 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 204 226 (accept_3_3 17 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 204 226 2 8 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 204 226 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 204 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 226 2 7 102 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 226 2 6 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 226 (accept_3_3 11 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 226 2 5 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 226 (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 204 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 226 2 4 102 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 226 2 3 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 226 (accept_3_3 5 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 226 2 2 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 204 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 226 2 1 102 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 226
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 204 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 226))))))))))))))))))))))) (allB_succ' 24 203 226 (Eq.refl Bool.true) (allA_of_3_1 24 203 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 202 226 (Eq.refl Bool.true) (allA_succ_of_gcd 24 202 226 2 12 101 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 202 226
  (accept_3_3 23 202 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 202 226 2 11 101 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 202 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 202 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 202 226 2 10 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 202 226 (Polychromatic418967fa.accept_21_19_13_16_1_7317 19 202 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 202 226 2 9 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 202 226 (accept_3_3 17 202 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 202 226 2 8 101 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 202 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 202 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 202 226 2 7 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 202 226 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 202 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 202 226 2 6 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 202 226 (accept_3_3 11 202 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 202 226 2 5 101 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 202 226
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 202 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 202 226 2 4 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 202 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 202 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 202 226 2 3 101 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 202 226 (accept_3_3 5 202 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 202 226 2 2 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 202 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  202 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 226 2 1 101 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 202 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 226))))))))))))))))))))))))) (allB_succ' 26 201 226 (Eq.refl Bool.true) (allA_succ_of_accept 25 201 226
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 201 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 226 (accept_3_3 23 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 201 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 201 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 226 (Polychromatic418967fa.accept_14_7_5_2_1_2473
  21 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 226 (accept_3_3 20
  201 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 201 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 226 (accept_3_3 17 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 201 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 201 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 226 (accept_3_3 14
  201 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 226
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 226 (accept_3_3 11 201 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 201 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 201 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 226 (Polychromatic418967fa.accept_11_9_3_6_1_797 9
  201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 226 (accept_3_3 8 201
  226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 226 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 226 (accept_3_3 5 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 201 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 226 (accept_3_3 2 201 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 226)))))))))))))))))))))))))) (allB_succ' 27 200 226
  (Eq.refl Bool.true) (allA_of_3_1 27 200 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 199 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 199 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 226 (accept_3_3 26 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 199 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 226
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 226 (accept_3_3 23 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 226 (accept_3_3 20 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 199 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 226
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 226 (accept_3_3 17 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 226 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 226 (accept_3_3 14 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 226 (accept_3_3 11 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 226 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 226 (accept_3_3 8 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 226 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 199 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 226 (accept_3_3 5 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 199 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 226 (accept_3_3 2 199 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 226)))))))))))))))))))))))))))) (allB_succ' 29 198
  226 (Eq.refl Bool.true) (allA_succ_of_gcd 28 198 226 2 14 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 198
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 226 2 13 99 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 226
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 226 2 12 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 226 (accept_3_3 23 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 198 226 2 11 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 198 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 198 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 226 2 10 99 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 226
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 226 2 9 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 226 (accept_3_3 17 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 226 2 8 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 198 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 226 2 7 99 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 226
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 226 2 6 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 226 (accept_3_3 11 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 226 2 5 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 198 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 226 2 4 99 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 226
  (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 226 2 3 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 226 (accept_3_3 5 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  226 2 2 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 226 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 198 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 226 2 1 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 226 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 198 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 226))))))))))))))))))))))))))))) (allB_succ' 30 197
  226 (Eq.refl Bool.true) (allA_of_3_1 30 197 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 196 226
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 196 226 2 15 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 226 (accept_3_3 29 196 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 196 226 2 14 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 196 226 (Polychromatic418967fa.accept_19_8_6_17_1_5186 27 196 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 226 2 13 98 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 226
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 226 2 12 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 196 226 (accept_3_3 23 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 196 226 2 11 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 196 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 196 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 226 2 10 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 196 226 2 9 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 196 226 (accept_3_3 17 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 226 2 8 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 196 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 196 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 226 2 7 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 226 2 6 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 196 226 (accept_3_3 11 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 226 2 5 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 226 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 196 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 226 2 4 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 226 2 3 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 226 (accept_3_3 5 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  226 2 2 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 196 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 226 2 1 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 226 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 196 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 226))))))))))))))))))))))))))))))) (allB_succ' 32
  195 226 (Eq.refl Bool.true) (allA_succ_of_accept 31 195 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 195 226 (accept_3_3 29 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 195 226 (Polychromatic418967fa.accept_21_7_6_16_1_5834 28 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 195 226 (Polychromatic418967fa.accept_18_9_15_10_1_395 27 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 226 (accept_3_3 26 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 195 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 195 226 (accept_3_3 23 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 195 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 195 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 226 (accept_3_3 20 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 226 (accept_3_3 17 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 195 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 195 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 226 (accept_3_3 14 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 226 (accept_3_3 11 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 195 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 195 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 226 (accept_3_3 8 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 226 (accept_3_3 5 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 195 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 226 (accept_3_3 2 195 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 226)))))))))))))))))))))))))))))))) (allB_succ' 33
  194 226 (Eq.refl Bool.true) (allA_of_3_1 33 194 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 193 226
  (Eq.refl Bool.true) (allA_succ_of_accept 33 193 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 226 (accept_3_3 32 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 193 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 226 (accept_3_3 29 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 226 (accept_3_3 26 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 226
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 226 (accept_3_3 23 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 226 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 226 (accept_3_3 20 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 226
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 226 (accept_3_3 17 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 226 (accept_3_3 14 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 226 (accept_3_3 11 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 226 (accept_3_3 8 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 226 (accept_3_3 5 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 193 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 226 (accept_3_3 2 193 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 226 (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 193 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 226)))))))))))))))))))))))))))))))))) (allB_succ' 35
  192 226 (Eq.refl Bool.true) (allA_succ_of_gcd 34 192 226 2 17 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 192 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 226 2 16 96 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 226 2 15 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 226 (accept_3_3 29 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 226 2 14 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 192 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 192 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 226 2 13 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 226 2 12 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 226 (accept_3_3 23 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 226 2 11 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 192 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 192 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 226 2 10 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 226 2 9 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 226 (accept_3_3 17 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 226 2 8 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 192 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 192 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 226 2 7 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 226 2 6 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 226 (accept_3_3 11 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 226 2 5 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 192 226 (Polychromatic418967fa.accept_18_9_12_10_1_387 9 192 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 226 2 4 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 226 2 3 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 226 (accept_3_3 5 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192
  226 2 2 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  192 226 (Polychromatic418967fa.accept_19_3_2_17_1_6574 3 192 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 192 226 2 1 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 192 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 192 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 226))))))))))))))))))))))))))))))))))) (allB_succ'
  36 191 226 (Eq.refl Bool.true) (allA_of_3_1 36 191 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 190 226
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 190 226 2 18 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 190 226 (accept_3_3 35 190 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 190 226 2 17 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 190 226 (Polychromatic418967fa.accept_23_10_6_19_1_11862 33 190 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 226 2 16 95 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 226 2 15 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 226 (accept_3_3 29 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 226 2 14 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 190 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 226 2 13 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 226
  (Polychromatic418967fa.accept_13_12_8_5_1_976 25 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 226 2 12 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 226 (accept_3_3 23 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 226 2 11 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 226 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 190 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 226 2 10 95 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 226
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 226 2 9 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 226 (accept_3_3 17 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 226 2 8 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 226 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 190 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 226 2 7 95 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 226 2 6 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 226 (accept_3_3 11 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 226 2 5 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 226 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 190 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 226 2 4 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 226
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 226 2 3 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 226 (accept_3_3 5 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  226 2 2 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 190 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 226 2 1 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 226 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 190 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 226))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 189 226 (Eq.refl Bool.true) (allA_succ_of_accept 37 189 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 226
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 189 226 (accept_3_3 35 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 189 226 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 189 226 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 226 (accept_3_3 32 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 189 226 (accept_3_3 29 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 189 226 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 226 (accept_3_3 26 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 226
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 226 (accept_3_3 23 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 226 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 226 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 226 (accept_3_3 20 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 226 (accept_3_3 17 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 226 (Polychromatic418967fa.accept_17_16_2_5_1_6031 16 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 226 (accept_3_3 14 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 226
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 189 226 (accept_3_3 11 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 189 226 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 189 226 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 226 (accept_3_3 8 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 226 (accept_3_3 5 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 226 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 189 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 226 (accept_3_3 2 189 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 226))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 188 226 (Eq.refl Bool.true) (allA_of_3_1 39 188 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 187 226 (Eq.refl Bool.true) (allA_succ_of_accept 39 187 226 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 226 (accept_3_3 38
  187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 187 226 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 187 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 226 (accept_3_3 35 187 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 187 226 (Polychromatic418967fa.accept_21_13_19_16_1_721 34 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 226 (accept_3_3 32 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 226 (accept_3_3 29 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 226 (accept_3_3 26 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 226 (accept_3_3 23 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 226 (accept_3_3 20 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 226 (Polychromatic418967fa.accept_20_19_7_6_1_6255 19 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 226 (accept_3_3 17 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 226 (accept_3_3 14 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 226 (accept_3_3 11 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 226 (accept_3_3 8 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 226 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 226 (accept_3_3 5 187 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 187 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 226 (accept_3_3 2 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 226)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 186 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 186 226 2 20 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 186 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 226 2 19 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 226
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 226 2 18 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 226 (accept_3_3 35 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 226 2 17 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 186 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 226 2 16 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 226 2 15 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 226 (accept_3_3 29 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 226 2 14 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 186 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 226 2 13 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 226 2 12 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 226 (accept_3_3 23 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 226 2 11 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 186 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 226 2 10 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 226 2 9 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 226 (accept_3_3 17 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 226 2 8 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 186 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 226 2 7 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 226 2 6 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 226 (accept_3_3 11 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 226 2 5 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 186 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 226 2 4 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 226 2 3 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 226 (accept_3_3 5 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  226 2 2 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 186 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 226 2 1 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 226 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 186 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 226)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 185 226 (Eq.refl Bool.true) (allA_of_3_1 42 185 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 184 226 (Eq.refl Bool.true) (allA_succ_of_gcd 42 184 226 2 21 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 226 (accept_3_3 41 184 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 226 2 20 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 39
  184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 226 2 19 92 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 184 226 2 18 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 184 226 (accept_3_3 35 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 184 226 2 17 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 184 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 184 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 226 2 16 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 226 2 15 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 226 (accept_3_3 29 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 226 2 14 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 184 226 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 184 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 226 2 13 92 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 226 2 12 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 184 226 (accept_3_3 23 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 184 226 2 11 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 184 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 226 2 10 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 226 2 9 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 226 (accept_3_3 17 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 226 2 8 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 184 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 184 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 226 2 7 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 226 2 6 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 184 226 (accept_3_3 11 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 226 2 5 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 226 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 184 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 226 2 4 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 226 2 3 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 226 (accept_3_3 5 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  226 2 2 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 184 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 226 2 1 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 226 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 184 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 226)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 183 226 (Eq.refl Bool.true) (allA_succ_of_accept 43 183 226 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 226 (accept_3_3 41 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 226 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 226 (accept_3_3 38 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 183 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 226
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 226 (accept_3_3 35 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 226 (accept_3_3 32 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 226 (accept_3_3 29 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 226 (accept_3_3 26 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 226 (accept_3_3 23 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 226 (accept_3_3 20 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 226
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 226 (accept_3_3 17 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 226 (accept_3_3 14 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 226
  (Polychromatic418967fa.accept_11_1_7_6_1_378 12 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 226 (accept_3_3 11 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 226 (accept_3_3 8 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 226 (accept_3_3 5 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 183 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 226 (accept_3_3 2 183 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 226))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 182 226 (Eq.refl Bool.true) (allA_of_3_1 45 182 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 181 226 (Eq.refl Bool.true) (allA_succ_of_accept 45 181 226 (Polychromatic418967fa.accept_6_3_1_4_1_25
  45 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 226 (accept_3_3 44
  181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 181 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 181 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 226 (accept_3_3 41 181 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 181 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 226 (accept_3_3 38 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 226 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 226 (accept_3_3 35 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 226 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 226 (accept_3_3 32 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 226 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 226 (accept_3_3 29 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 181
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 226 (accept_3_3 26 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 226 (accept_3_3 23 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 226 (accept_3_3 20 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 226 (accept_3_3 17 181 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 226 (accept_3_3 14 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 226 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 226 (accept_3_3 11 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 181 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 226 (accept_3_3 8 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 226 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 226 (accept_3_3 5 181 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 181 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 226 (accept_3_3 2 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 226)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 180 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 180 226 2 23 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 180 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 180 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 180 226 2 22 90 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 226
  (Polychromatic418967fa.accept_25_18_5_1_1_13520 43 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 180 226 2 21 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 180 226 (accept_3_3 41 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 226 2 20 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 180 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 226 2 19 90 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 226
  (Polychromatic418967fa.accept_25_12_5_1_1_13519 37 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 180 226 2 18 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 180 226 (accept_3_3 35 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 180 226 2 17 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 180 226 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 226 2 16 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 226 2 15 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 226 (accept_3_3 29 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 226 2 14 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 180 226 (Polychromatic418967fa.accept_19_8_9_17_1_5151 27 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 226 2 13 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 226 2 12 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 226 (accept_3_3 23 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 226 2 11 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 180 226 (Polychromatic418967fa.accept_14_7_12_2_1_2502 21 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 226 2 10 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 226
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 226 2 9 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 226 (accept_3_3 17 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 226 2 8 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 180 226 (Polychromatic418967fa.accept_17_15_10_5_1_1573 15 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 226 2 7 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 226
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 226 2 6 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 226 (accept_3_3 11 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 226 2 5 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 226 (Polychromatic418967fa.accept_21_9_12_16_1_13518 9 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 226 2 4 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 226
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 226 2 3 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 226 (accept_3_3 5 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180
  226 2 2 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  180 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 180 226 2 1 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 180 226 (Polychromatic418967fa.accept_19_1_9_17_1_8039 1 180 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 226)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 179 226 (Eq.refl Bool.true) (allA_of_3_1 48 179 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 178 226 (Eq.refl Bool.true) (allA_succ_of_gcd 48 178 226 2 24 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 178 226 (accept_3_3 47 178 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 178 226 2 23 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 178 226
  (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 178 226 2 22 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 178 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 178 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 178 226 2 21 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 178 226 (accept_3_3 41 178 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 178 226 2 20 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 178 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 178 226 2 19 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 178 226 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 178 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 178 226 2 18 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 178 226 (accept_3_3 35 178 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 178 226 2 17 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 178 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 226 2 16 89 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 226 2 15 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 226 (accept_3_3 29 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 226 2 14 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 178 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 226 2 13 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 226
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 178 226 2 12 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 178 226 (accept_3_3 23 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 226 2 11 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 178 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 226 2 10 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 226 2 9 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 226 (accept_3_3 17 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 226 2 8 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 178 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 226 2 7 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 226 2 6 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 226 (accept_3_3 11 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 226 2 5 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 226 (Polychromatic418967fa.accept_19_9_7_17_1_3875 9 178 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 226 2 4 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 226
  (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 226 2 3 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 226 (accept_3_3 5 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  226 2 2 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 178 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 226 2 1 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 178 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 226)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 177 226 (Eq.refl Bool.true) (allA_succ_of_accept 49 177 226 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 177 226 (accept_3_3 47 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 177 226 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 177 226 (Polychromatic418967fa.accept_17_11_7_5_1_1567 45 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 226 (accept_3_3 44 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 177 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 226 (accept_3_3 41 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 226 (accept_3_3 38 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 226
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 226 (accept_3_3 35 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 226 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 226 (accept_3_3 32 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 226 (accept_3_3 29 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 226 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 226 (accept_3_3 26 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 226
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 226 (accept_3_3 23 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 177 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 177 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 226 (accept_3_3 20 177 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 226
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 226 (accept_3_3 17 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 226 (accept_3_3 14 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 226 (accept_3_3 11 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 226 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 226 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 226 (accept_3_3 8 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 226 (accept_3_3 5 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 177 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 226 (accept_3_3 2 177 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  226)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 176 226 (Eq.refl Bool.true) (allA_of_3_1 51 176
  226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 175 226 (Eq.refl Bool.true) (allA_succ_of_accept 51 175
  226 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 226 (accept_3_3 50 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 226 (accept_3_3 47 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 226 (Polychromatic418967fa.accept_19_8_4_17_1_9510 46 175 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 226 (accept_3_3 44 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 226 (accept_3_3 41 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 226 (accept_3_3 38 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 226 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 226 (accept_3_3 35 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 175 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 226 (accept_3_3 32 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 226 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 226 (accept_3_3 29 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 226 (accept_3_3 26 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 226 (accept_3_3 23 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 226 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 175 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 226 (accept_3_3 20 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 226 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 226 (Polychromatic418967fa.accept_19_18_4_17_1_2618 18 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 226 (accept_3_3 17 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 226 (accept_3_3 14 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 226 (accept_3_3 11 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 226 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 175 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 226 (accept_3_3 8 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 226 (accept_3_3 5 175 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 226 (accept_3_3 2 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 226)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 174 226 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 174 226 2 26 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 174 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 174 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 174 226 2 25 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 226 2 24 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 226 (accept_3_3 47 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 226 2 23 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 174 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 226 2 22 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 226 2 21 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 226 (accept_3_3 41 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 226 2 20 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 174 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 226 2 19 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 226
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 226 2 18 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 226 (accept_3_3 35 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 226 2 17 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 174 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 226 2 16 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 226 2 15 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 226 (accept_3_3 29 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 226 2 14 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 174 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 226 2 13 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 226 2 12 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 226 (accept_3_3 23 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 226 2 11 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 174 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 226 2 10 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 226
  (Polychromatic418967fa.accept_20_19_14_6_1_4726 19 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 174 226 2 9 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 174 226 (accept_3_3 17 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 226 2 8 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 174 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 226 2 7 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 226 2 6 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 226 (accept_3_3 11 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 226 2 5 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 174 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 226 2 4 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 226 2 3 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 226 (accept_3_3 5 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  226 2 2 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 174 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 226 2 1 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  226))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 173 226 (Eq.refl Bool.true) (allA_of_3_1 54
  173 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 172 226 (Eq.refl Bool.true) (allA_succ_of_gcd 54 172
  226 2 27 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 172 226 (accept_3_3 53 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 172 226 2 26 86 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 172 226
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 172 226 2 25 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 172 226 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 172 226 2 24 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 172 226 (accept_3_3 47 172 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 172 226 2 23 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 172 226
  (Polychromatic418967fa.accept_11_1_7_6_1_378 45 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 172 226 2 22 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 172 226 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 172 226 2 21 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 172 226 (accept_3_3 41 172 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 172 226 2 20 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 172 226
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 172 226 2 19 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 172 226 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 172 226 2 18 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 172 226 (accept_3_3 35 172 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 172 226 2 17 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 172 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 172 226 2 16 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 172 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 172 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 226 2 15 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 226 (accept_3_3 29 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 226 2 14 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 226 2 13 86 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 226 2 12 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 226 (accept_3_3 23 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 226 2 11 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 172 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 226 2 10 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 226 2 9 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 226 (accept_3_3 17 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 226 2 8 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 226 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 226 2 7 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 226 2 6 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 226 (accept_3_3 11 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 226 2 5 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 226 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 172 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 226 2 4 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 226 2 3 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 226 (accept_3_3 5 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  226 2 2 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 226 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 172 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 226 2 1 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 171 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 171 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 171 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 226 (accept_3_3 53 171 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 226 (Polychromatic418967fa.accept_10_2_1_6_1_634
  52 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 226
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 171 226 (accept_3_3 50 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 171 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 171 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 226 (accept_3_3 47 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 226 (Polychromatic418967fa.accept_13_7_2_5_1_2344 46 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 171 226 (accept_3_3 44 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 171 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 171 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 226 (accept_3_3 41 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 171 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 226
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 226 (accept_3_3 38 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 171 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 226 (accept_3_3 35 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 226 (accept_3_3 32 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 226 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 226 (accept_3_3 29 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 226 (Polychromatic418967fa.accept_21_7_3_16_1_7337 28 171
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 226 (accept_3_3 26 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 226 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 226 (accept_3_3 23 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 171 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 226 (accept_3_3 20 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 226 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 226 (accept_3_3 17 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 226 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 171
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 226 (accept_3_3 14 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 226 (accept_3_3 11 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 226 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 171 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 226 (accept_3_3 8 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 226 (accept_3_3 5 171 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 226 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 171 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 226
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 226 (accept_3_3 2 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 226)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 170 226 (Eq.refl
  Bool.true) (allA_of_3_1 57 170 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 169 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 169 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 226 (accept_3_3 56 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 226 (Polychromatic418967fa.accept_16_6_9_2_1_6518
  54 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 226 (accept_3_3 53
  169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 226 (accept_3_3 50 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 169 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 226 (Polychromatic418967fa.accept_7_6_1_2_1_230
  48 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 226 (accept_3_3 47
  169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 226
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 169 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 226 (accept_3_3 44 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 226 (Polychromatic418967fa.accept_9_6_7_1_1_145
  42 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 226 (accept_3_3 41
  169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 40 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 226 (accept_3_3 38 169 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 169 226 (Polychromatic418967fa.accept_20_17_9_6_1_6219 37 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 226
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 226 (accept_3_3 35 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 226 (accept_3_3 32 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 226 (accept_3_3 29 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 226 (accept_3_3 26 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 226 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 226 (accept_3_3 23 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 226 (accept_3_3 20 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 226
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 226 (accept_3_3 17 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 226 (accept_3_3 14 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 226 (accept_3_3 11 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 226 (accept_3_3 8 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 226 (accept_3_3 5 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 226 (accept_3_3 2 169 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 226 (Polychromatic418967fa.accept_16_1_9_2_1_4161 1 169 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 168 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 168 226 2 29 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 168 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 168 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 226 2 28 84 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 226
  (Polychromatic418967fa.accept_25_5_18_1_1_13517 55 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 168 226 2 27 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 168 226 (accept_3_3 53 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 226 2 26 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 168 226 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 168 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 226 2 25 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 226 2 24 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 226 (accept_3_3 47 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 226 2 23 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 226 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 168 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 226 2 22 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 226 2 21 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 226 (accept_3_3 41 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 226 2 20 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 168 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 168 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 226 2 19 84 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 226
  (Polychromatic418967fa.accept_19_18_16_17_1_2626 37 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 226 2 18 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 226 (accept_3_3 35 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 226 2 17 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 168 226 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 168 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 226 2 16 84 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 226 2 15 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 226 (accept_3_3 29 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 226 2 14 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 168 226 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 168 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 226 2 13 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 226 2 12 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 226 (accept_3_3 23 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 226 2 11 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 168 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 168 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 226 2 10 84 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 226
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 226 2 9 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 226 (accept_3_3 17 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 226 2 8 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 168 226 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 168 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 226 2 7 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 226 2 6 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 226 (accept_3_3 11 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 226 2 5 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 168 226 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 168 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 226 2 4 84 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 226 2 3 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 226 (accept_3_3 5 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168
  226 2 2 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  168 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 168 226 2 1 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 168 226 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 168 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 167 226 (Eq.refl Bool.true) (allA_of_3_1
  60 167 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 166 226 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  166 226 2 30 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 166 226 (accept_3_3 59 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  166 226 2 29 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 166 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 166 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 226 2 28 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 226
  (Polychromatic418967fa.accept_21_13_19_16_1_721 55 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 166 226 2 27 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 166 226 (accept_3_3 53 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 226 2 26 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 226 2 25 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 226
  (Polychromatic418967fa.accept_11_5_1_6_1_774 49 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 226 2 24 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 226 (accept_3_3 47 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 226 2 23 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 226 2 22 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 226 2 21 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 226 (accept_3_3 41 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 226 2 20 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 226 2 19 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 226
  (Polychromatic418967fa.accept_22_15_12_6_1_8744 37 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 166 226 2 18 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 166 226 (accept_3_3 35 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 226 2 17 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 226 2 16 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 226 2 15 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 226 (accept_3_3 29 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 226 2 14 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 226 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 226 2 13 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 226 2 12 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 226 (accept_3_3 23 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 226 2 11 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 226 2 10 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 226
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 226 2 9 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 226 (accept_3_3 17 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 226 2 8 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 226 2 7 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 226
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 166 226 2 6 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 226 (accept_3_3 11 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 226 2 5 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 226 (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 166 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 226 2 4 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 226 2 3 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 226 (accept_3_3 5 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  226 2 2 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 166 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 226 2 1 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 226 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1 166 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 165 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 165 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 226 (accept_3_3 59 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 226 (Polychromatic418967fa.accept_9_4_3_1_1_154
  58 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 226
  (Polychromatic418967fa.accept_21_15_18_16_1_2942 57 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 226 (accept_3_3 56 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 165 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 226 (accept_3_3 53 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 226 (Polychromatic418967fa.accept_9_7_3_1_1_386
  52 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 165 226 (accept_3_3 50 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 165 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 226 (accept_3_3 47 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 226 (Polychromatic418967fa.accept_22_2_11_6_1_10477 46 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 226
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 165 226 (accept_3_3 44 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 165 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 165 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 226 (accept_3_3 41 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 226 (accept_3_3 38 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 226 (Polychromatic418967fa.accept_21_15_18_16_1_2942 36 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 226 (accept_3_3 35 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 226 (accept_3_3 32 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 226 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 226 (accept_3_3 29 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 226 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 165
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 226 (accept_3_3 26 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 226 (accept_3_3 23 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 226
  (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 226 (accept_3_3 20 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 226 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 226 (accept_3_3 17 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 226 (accept_3_3 14 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 226 (accept_3_3 11 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 226 (Polychromatic418967fa.accept_17_10_12_5_1_6028 10 165 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 226
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 226 (accept_3_3 8 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 226 (accept_3_3 5 165 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 165 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 226 (accept_3_3 2 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 164 226
  (Eq.refl Bool.true) (allA_of_3_1 63 164 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 163 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 226 (accept_3_3 62 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 226
  (Polychromatic418967fa.accept_14_4_9_2_1_95 60 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 226 (accept_3_3 59 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 226 (accept_3_3 56 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 226
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 226 (accept_3_3 53 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 226 (accept_3_3 50 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 226
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 226 (accept_3_3 47 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 226 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 226 (accept_3_3 44 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 226 (Polychromatic418967fa.accept_19_5_11_17_1_6536 43 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 226
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 163 226 (accept_3_3 41 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 163 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 163 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 226 (accept_3_3 38 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 226
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 226 (accept_3_3 35 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 226 (Polychromatic418967fa.accept_18_16_1_10_1_2029 34 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 226 (accept_3_3 32 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 226 (Polychromatic418967fa.accept_16_15_3_2_1_4170 31 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 226
  (Polychromatic418967fa.accept_17_13_10_5_1_2566 30 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 163 226 (accept_3_3 29 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 163 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 226 (accept_3_3 26 163 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 226
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 226 (accept_3_3 23 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 226 (Polychromatic418967fa.accept_16_6_3_2_1_3096 22 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 226 (accept_3_3 20 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 226 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 226
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 226 (accept_3_3 17 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 226 (accept_3_3 14 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 226
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 226 (accept_3_3 11 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 226 (accept_3_3 8 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 226 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 226
  (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 226 (accept_3_3 5 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 163 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 226 (accept_3_3 2 163 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 162 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 162 226 2 32 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 226 2 31 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 226
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 226 2 30 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 226 (accept_3_3 59 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 226 2 29 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 226 2 28 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 226 2 27 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 226 (accept_3_3 53 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 226 2 26 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 162 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 226 2 25 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 226
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 226 2 24 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 226 (accept_3_3 47 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 226 2 23 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 162 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 226 2 22 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 226
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 226 2 21 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 226 (accept_3_3 41 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 226 2 20 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 226 2 19 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 226
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 37 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 226 2 18 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 226 (accept_3_3 35 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 226 2 17 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 226 2 16 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 226 2 15 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 226 (accept_3_3 29 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 226 2 14 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 162 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 226 2 13 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 226
  (Polychromatic418967fa.accept_11_3_8_6_1_788 25 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 226 2 12 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 226 (accept_3_3 23 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 226 2 11 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 226 2 10 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 226
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 226 2 9 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 226 (accept_3_3 17 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 226 2 8 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 226 2 7 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 226 2 6 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 226 (accept_3_3 11 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 226 2 5 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 162 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 226 2 4 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 226
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 7 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 226 2 3 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 226 (accept_3_3 5 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  226 2 2 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 226 2 1 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 161 226 (Eq.refl Bool.true)
  (allA_of_3_1 66 161 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 160 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 160 226 2 33 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 160 226 (accept_3_3 65 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 160 226 2 32 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 160 226 (Polychromatic418967fa.accept_17_12_7_5_1_8659 63 160 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 226 2 31 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 160 226 2 30 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 160 226 (accept_3_3 59 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 226 2 29 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 226 2 28 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 226 2 27 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 226 (accept_3_3 53 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 226 2 26 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 226 2 25 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 226 2 24 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 226 (accept_3_3 47 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 226 2 23 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 226 2 22 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 160 226 2 21 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 160 226 (accept_3_3 41 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 226 2 20 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 226 2 19 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 226 2 18 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 160 226 (accept_3_3 35 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 160 226 2 17 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 226 2 16 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 226 2 15 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 226 (accept_3_3 29 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 226 2 14 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 226 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 226 2 13 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 226 2 12 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 160 226 (accept_3_3 23 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 226 2 11 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 226 2 10 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 226 2 9 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 226 (accept_3_3 17 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 226 2 8 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 160 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 226 2 7 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 226 2 6 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 160 226 (accept_3_3 11 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 226 2 5 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 226 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 160 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 226 2 4 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 226 2 3 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 226 (accept_3_3 5 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  226 2 2 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 160 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 226 2 1 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 160 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 160 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 159 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 159 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 159 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 226 (accept_3_3 65 159 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 226
  (Polychromatic418967fa.accept_24_16_15_10_1_4733 64 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 226 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 226 (accept_3_3 62 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 226 (accept_3_3 59 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 226 (accept_3_3 56 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 226
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 226 (accept_3_3 53 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 226 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 226 (accept_3_3 50 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 159 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 226 (accept_3_3 47 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 226 (accept_3_3 44 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 226 (accept_3_3 41 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 226 (accept_3_3 38 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 226
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 226 (accept_3_3 35 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 226 (accept_3_3 32 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 226 (accept_3_3 29 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 226 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 226 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 226 (accept_3_3 26 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 226 (accept_3_3 23 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 226 (accept_3_3 20 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 226 (accept_3_3 17 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 226 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 226 (accept_3_3 14 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 226 (accept_3_3 11 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 226 (accept_3_3 8 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 226 (accept_3_3 5 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 226 (accept_3_3 2 159 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 158 226 (Eq.refl Bool.true)
  (allA_of_3_1 69 158 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 157 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 226 (accept_3_3 68 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 226 (accept_3_3 65
  157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 226 (accept_3_3 62 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 157 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 226 (Polychromatic418967fa.accept_9_6_4_1_1_390
  60 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 226 (accept_3_3 59
  157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 226
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 58 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 226 (accept_3_3 56 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 226 (Polychromatic418967fa.accept_7_5_3_2_1_249
  54 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 226 (accept_3_3 53
  157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 52 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 226 (accept_3_3 50 157 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 157 226 (Polychromatic418967fa.accept_19_11_5_17_1_2620 49 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 226 (accept_3_3 47 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 226 (Polychromatic418967fa.accept_21_4_10_16_1_13516 46 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 226 (accept_3_3 44 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 226
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 226 (accept_3_3 41 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 226 (accept_3_3 38 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 226 (Polychromatic418967fa.accept_16_5_13_2_1_2138 37 157 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 226 (accept_3_3 35 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 226 (accept_3_3 32 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 226 (accept_3_3 29 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 226 (accept_3_3 26 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 226
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 226 (accept_3_3 23 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 226 (accept_3_3 20 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 226
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 18 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 226 (accept_3_3 17 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 226 (accept_3_3 14 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 226 (accept_3_3 11 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 226 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 226 (accept_3_3 8 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 226 (accept_3_3 5 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 157 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 226 (accept_3_3 2 157 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 156 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 156 226 2 35 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 226 2 34 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 226 2 33 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 226 (accept_3_3 65 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 226 2 32 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 156 226 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 226 2 31 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 226 2 30 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 226 (accept_3_3 59 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 226 2 29 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 226 (Polychromatic418967fa.accept_16_9_12_2_1_3093 57 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 226 2 28 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 226
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 226 2 27 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 226 (accept_3_3 53 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 226 2 26 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 226 2 25 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 226 2 24 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 226 (accept_3_3 47 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 226 2 23 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 226 (Polychromatic418967fa.accept_18_9_12_10_1_387 45 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 226 2 22 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 226 2 21 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 226 (accept_3_3 41 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 226 2 20 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 226 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 226 2 19 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 226
  (Polychromatic418967fa.accept_11_4_2_6_1_389 37 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 226 2 18 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 226 (accept_3_3 35 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 226 2 17 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 156 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 226 2 16 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 226 2 15 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 226 (accept_3_3 29 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 226 2 14 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 156 226 (Polychromatic418967fa.accept_18_9_12_10_1_387 27 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 226 2 13 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 226 2 12 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 226 (accept_3_3 23 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 226 2 11 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 226 (Polychromatic418967fa.accept_19_2_4_17_1_12087 21 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 226 2 10 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 226
  (Polychromatic418967fa.accept_17_2_3_5_1_763 19 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 226 2 9 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 226 (accept_3_3 17 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 226 2 8 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 156 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 226 2 7 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 226 2 6 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 226 (accept_3_3 11 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 226 2 5 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 226 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 226 2 4 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 226 2 3 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 226 (accept_3_3 5 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156
  226 2 2 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  156 226 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 156 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 156 226 2 1 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 156 226 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 156 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 155 226 (Eq.refl Bool.true)
  (allA_of_3_1 72 155 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 154 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 154 226 2 36 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 226 (accept_3_3 71 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 226 2 35 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 226 (Polychromatic418967fa.accept_19_12_2_17_1_5210 69 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 226 2 34 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 226
  (Polychromatic418967fa.accept_17_16_1_5_1_2600 67 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 226 2 33 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 226 (accept_3_3 65 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 226 2 32 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 226 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 226 2 31 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 226
  (Polychromatic418967fa.accept_19_4_2_17_1_3870 61 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 226 2 30 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 226 (accept_3_3 59 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 226 2 29 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 226 (Polychromatic418967fa.accept_15_12_4_1_1_3746 57 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 226 2 28 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 226
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 226 2 27 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 226 (accept_3_3 53 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 226 2 26 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 226 (Polychromatic418967fa.accept_20_11_14_6_1_4714 51 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 226 2 25 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 226
  (Polychromatic418967fa.accept_20_9_14_6_1_320 49 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 226 2 24 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 226 (accept_3_3 47 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 226 2 23 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 226 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 154 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 226 2 22 77 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 226
  (Polychromatic418967fa.accept_19_5_2_17_1_8066 43 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 226 2 21 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 226 (accept_3_3 41 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 226 2 20 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 226 (Polychromatic418967fa.accept_20_19_14_6_1_4726 39 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 226 2 19 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 226
  (Polychromatic418967fa.accept_25_12_4_1_1_11755 37 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 154 226 2 18 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 154 226 (accept_3_3 35 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 226 2 17 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 226 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 226 2 16 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 226
  (Polychromatic418967fa.accept_19_12_2_17_1_5210 31 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 154 226 2 15 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 154 226 (accept_3_3 29 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 226 2 14 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 226 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 226 2 13 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 226
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 226 2 12 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 226 (accept_3_3 23 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 226 2 11 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 226 (Polychromatic418967fa.accept_17_4_1_5_1_2554 21 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 226 2 10 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 226
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 226 2 9 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 226 (accept_3_3 17 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 226 2 8 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 226 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 154 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 226 2 7 77 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 226
  (Polychromatic418967fa.accept_21_13_7_16_1_7351 13 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 154 226 2 6 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 154 226 (accept_3_3 11 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 226 2 5 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 226 (Polychromatic418967fa.accept_19_9_2_17_1_10805 9 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 226 2 4 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 226
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 226 2 3 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 226 (accept_3_3 5 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  226 2 2 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 226 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 154 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 226 2 1 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 226 (Polychromatic418967fa.accept_20_1_14_6_1_4725 1 154 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 153 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 226
  (Polychromatic418967fa.accept_19_15_1_17_1_670 72 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 226 (accept_3_3 71 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 153 226 (Polychromatic418967fa.accept_16_6_9_2_1_6518 70 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 226 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 226 (accept_3_3 68 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 153 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 153 226 (accept_3_3 65 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 153 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 226 (accept_3_3 62 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 153 226 (accept_3_3 59 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 153 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 153 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 226 (accept_3_3 56 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 226 (accept_3_3 53 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 226 (accept_3_3 50 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 226
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 153 226 (accept_3_3 47 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 153 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 153 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 226 (accept_3_3 44 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 226 (accept_3_3 41 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 226 (Polychromatic418967fa.accept_33_7_21_28_1_3910 40 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 226 (accept_3_3 38 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 226 (accept_3_3 35 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 226 (Polychromatic418967fa.accept_13_8_10_5_1_977 34 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 226 (Polychromatic418967fa.accept_16_1_9_2_1_4161 33 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 226 (accept_3_3 32 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 226 (accept_3_3 29 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 226 (accept_3_3 26 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 226 (accept_3_3 23 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 226 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 226 (accept_3_3 20 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 226 (accept_3_3 17 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 226 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 226 (accept_3_3 14 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 226
  (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 226 (accept_3_3 11 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 226 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 226 (accept_3_3 8 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 226 (accept_3_3 5 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 226 (accept_3_3 2 153 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 152 226 (Eq.refl
  Bool.true) (allA_of_3_1 75 152 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 151 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 226 (accept_3_3 74 151 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 226 (Polychromatic418967fa.accept_10_2_1_6_1_634
  72 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 226 (accept_3_3 71
  151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 226
  (Polychromatic418967fa.accept_19_13_18_17_1_5141 70 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 226 (accept_3_3 68 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 226 (accept_3_3 65 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 226 (accept_3_3 62 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 226
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 226 (accept_3_3 59 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 226 (accept_3_3 56 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 226 (accept_3_3 53 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 226 (accept_3_3 50 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 226 (accept_3_3 47 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 226 (Polychromatic418967fa.accept_22_2_19_6_1_5421 46 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 226 (accept_3_3 44 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 226 (Polychromatic418967fa.accept_16_11_7_2_1_4185 43 151 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 226
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 226 (accept_3_3 41 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 226 (accept_3_3 38 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 226
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 226 (accept_3_3 35 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 226 (accept_3_3 32 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 226 (accept_3_3 29 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 226 (accept_3_3 26 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 226
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 226 (accept_3_3 23 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 226 (accept_3_3 20 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 226
  (Polychromatic418967fa.accept_24_18_7_10_1_13515 18 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 151 226 (accept_3_3 17 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 151 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 151 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 226 (accept_3_3 14 151 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 226 (accept_3_3 11 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 226 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 226 (accept_3_3 8 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 226 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 226 (accept_3_3 5 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 226 (accept_3_3 2 151 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 150 226 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 150 226 2 38 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 150 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 150 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 150 226 2 37 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 226
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 73 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 226 2 36 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 226 (accept_3_3 71 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 226 2 35 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 226 2 34 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 226 2 33 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 226 (accept_3_3 65 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 226 2 32 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 150 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 226 2 31 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 226 2 30 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 226 (accept_3_3 59 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 226 2 29 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 226 2 28 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 226 2 27 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 226 (accept_3_3 53 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 226 2 26 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 150 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 226 2 25 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 226 2 24 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 226 (accept_3_3 47 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 226 2 23 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 226 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 226 2 22 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 226 2 21 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 226 (accept_3_3 41 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 226 2 20 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 226 2 19 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 226
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 226 2 18 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 226 (accept_3_3 35 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 226 2 17 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 226 2 16 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 226 2 15 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 226 (accept_3_3 29 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 226 2 14 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 226 2 13 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 226 2 12 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 226 (accept_3_3 23 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 226 2 11 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 226 2 10 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 226 2 9 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 226 (accept_3_3 17 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 226 2 8 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 226 2 7 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 226 2 6 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 226 (accept_3_3 11 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 226 2 5 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 150 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 226 2 4 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 226 2 3 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 226 (accept_3_3 5 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  226 2 2 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 226 2 1 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 150 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 149 226 (Eq.refl
  Bool.true) (allA_of_3_1 78 149 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 148 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 148 226 2 39 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 226 (accept_3_3 77 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 226 2 38 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 226 2 37 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 226 2 36 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 226 (accept_3_3 71 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 226 2 35 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 226 2 34 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 226
  (Polychromatic418967fa.accept_11_1_5_6_1_397 67 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 226 2 33 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 226 (accept_3_3 65 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 226 2 32 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 226 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 226 2 31 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 226 2 30 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 226 (accept_3_3 59 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 226 2 29 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 226 2 28 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 226 2 27 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 226 (accept_3_3 53 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 226 2 26 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 226 2 25 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 226 2 24 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 226 (accept_3_3 47 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 226 2 23 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 226 2 22 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 226 2 21 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 226 (accept_3_3 41 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 226 2 20 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 226 2 19 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 226 2 18 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 226 (accept_3_3 35 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 226 2 17 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 226 2 16 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 226 2 15 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 226 (accept_3_3 29 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 226 2 14 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 226 2 13 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 226 2 12 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 226 (accept_3_3 23 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 226 2 11 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 226 2 10 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 226 2 9 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 226 (accept_3_3 17 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 226 2 8 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 226 2 7 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 226 2 6 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 148 226 (accept_3_3 11 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 226 2 5 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 226 (Polychromatic418967fa.accept_17_9_12_5_1_219 9 148 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 226 2 4 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 226 2 3 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 226 (accept_3_3 5 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  226 2 2 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 226 2 1 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 226 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 148 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 147 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 226 (Polychromatic418967fa.accept_9_6_3_1_1_155
  78 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 226 (accept_3_3 77
  147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 76 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 147 226 (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 147 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 226 (accept_3_3 74 147 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 226
  (Polychromatic418967fa.accept_19_15_14_17_1_9486 72 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 147 226 (accept_3_3 71 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 147 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 226 (accept_3_3 68 147 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 226 (accept_3_3 65 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 226 (Polychromatic418967fa.accept_13_12_4_5_1_1637 64 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 226 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 226 (accept_3_3 62 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 147 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 226 (accept_3_3 59 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 147 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 226 (accept_3_3 56 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 226 (accept_3_3 53 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 226 (accept_3_3 50 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 226
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 147 226 (accept_3_3 47 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 147 226 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 226 (accept_3_3 44 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 147 226 (accept_3_3 41 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 147 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 147 226 (Polychromatic418967fa.accept_19_1_14_17_1_6605 39 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 226 (accept_3_3 38 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 226
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 147 226 (accept_3_3 35 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 147 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 226 (accept_3_3 32 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 226 (accept_3_3 29 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 226 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 226 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 226 (accept_3_3 26 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 226 (accept_3_3 23 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 226 (accept_3_3 20 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 226 (accept_3_3 17 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 226 (accept_3_3 14 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 226
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 226 (accept_3_3 11 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 226 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 226 (accept_3_3 8 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 226 (accept_3_3 5 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 226 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 226 (accept_3_3 2 147 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 146 226 (Eq.refl
  Bool.true) (allA_of_3_1 81 146 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 145 226 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 226 (accept_3_3 80 145 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 226
  (Polychromatic418967fa.accept_19_2_12_17_1_5197 78 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 145 226 (accept_3_3 77 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 145 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 145 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 145 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 226 (accept_3_3 74 145 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 73
  145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 226
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 226 (accept_3_3 71 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 226 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 226 (accept_3_3 68 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 226 (accept_3_3 65 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 226 (accept_3_3 62 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 226 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 226 (accept_3_3 59 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 226 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 226 (accept_3_3 56 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 226
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 226 (accept_3_3 53 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 226 (accept_3_3 50 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 226 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 226
  (Polychromatic418967fa.accept_11_4_2_6_1_389 48 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 226 (accept_3_3 47 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 226 (accept_3_3 44 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 226
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 226 (accept_3_3 41 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 226 (accept_3_3 38 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 226 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 226
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 226 (accept_3_3 35 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 226 (accept_3_3 32 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 226
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 226 (accept_3_3 29 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 226 (accept_3_3 26 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 226 (accept_3_3 23 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 226 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 226 (accept_3_3 20 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 226 (accept_3_3 17 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 226 (accept_3_3 14 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 226 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 145 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 226
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 226 (accept_3_3 11 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 226 (accept_3_3 8 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 226
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 226 (accept_3_3 5 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 226 (accept_3_3 2 145 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 226 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 145 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 144 226 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 144 226 2 41 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 144 226 (Polychromatic418967fa.accept_13_3_1_5_1_499 81 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 144 226 2 40 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 226
  (Polychromatic418967fa.accept_14_9_4_2_1_983 79 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 226 2 39 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 226 (accept_3_3 77 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 226 2 38 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 144 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 226 2 37 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 226
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 73 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 226 2 36 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 226 (accept_3_3 71 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 226 2 35 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 226 2 34 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 226
  (Polychromatic418967fa.accept_15_7_9_1_1_473 67 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 226 2 33 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 226 (accept_3_3 65 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 226 2 32 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 144 226 (Polychromatic418967fa.accept_17_12_8_5_1_6018 63 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 226 2 31 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 226 2 30 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 226 (accept_3_3 59 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 226 2 29 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 144 226 (Polychromatic418967fa.accept_21_15_18_16_1_2942 57 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 226 2 28 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 226 2 27 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 226 (accept_3_3 53 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 226 2 26 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 226 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 226 2 25 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 226
  (Polychromatic418967fa.accept_11_5_1_6_1_774 49 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 226 2 24 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 226 (accept_3_3 47 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 226 2 23 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 226 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 226 2 22 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 226
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 226 2 21 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 226 (accept_3_3 41 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 226 2 20 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 226 (Polychromatic418967fa.accept_22_17_12_6_1_13514 39 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 226 2 19 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 226
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 226 2 18 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 226 (accept_3_3 35 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 226 2 17 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 144 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 226 2 16 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 226
  (Polychromatic418967fa.accept_27_4_9_10_1_5610 31 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 226 2 15 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 226 (accept_3_3 29 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 226 2 14 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 144 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 226 2 13 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 226
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 226 2 12 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 226 (accept_3_3 23 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 226 2 11 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 226 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 226 2 10 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 226 2 9 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 226 (accept_3_3 17 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 226 2 8 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 144 226 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 226 2 7 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 226 2 6 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 226 (accept_3_3 11 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 226 2 5 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 144 226 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 144 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 226 2 4 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 226
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 226 2 3 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 226 (accept_3_3 5 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144
  226 2 2 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  144 226 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 144 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 144 226 2 1 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 144 226 (Polychromatic418967fa.accept_26_1_14_18_1_13513 1 144 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 143 226 (Eq.refl
  Bool.true) (allA_of_3_1 84 143 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 142 226 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 142 226 2 42 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 226 (accept_3_3 83 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 226 2 41 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 226 2 40 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 226
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 79 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 226 2 39 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 226 (accept_3_3 77 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 226 2 38 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 226 2 37 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 226
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 73 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 226 2 36 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 226 (accept_3_3 71 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 226 2 35 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 226 2 34 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 226 2 33 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 226 (accept_3_3 65 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 226 2 32 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 226 (Polychromatic418967fa.accept_19_6_9_17_1_5214 63 142 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 226 2 31 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 226
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 226 2 30 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 226 (accept_3_3 59 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 226 2 29 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 226 2 28 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 226
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 226 2 27 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 226 (accept_3_3 53 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 226 2 26 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 226 2 25 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 226 2 24 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 226 (accept_3_3 47 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 226 2 23 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 226 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 142 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 226 2 22 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 226
  (Polychromatic418967fa.accept_13_4_12_5_1_476 43 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 226 2 21 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 226 (accept_3_3 41 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 226 2 20 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 226 2 19 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 226
  (Polychromatic418967fa.accept_17_3_6_5_1_8669 37 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 226 2 18 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 226 (accept_3_3 35 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 226 2 17 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 226 2 16 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 226 2 15 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 226 (accept_3_3 29 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 226 2 14 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 226 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 142 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 226 2 13 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 226
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 226 2 12 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 226 (accept_3_3 23 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 226 2 11 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 226 2 10 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 226
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 226 2 9 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 226 (accept_3_3 17 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 226 2 8 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 226 2 7 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 226 2 6 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 226 (accept_3_3 11 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 226 2 5 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 226 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 142 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 226 2 4 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 226
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 226 2 3 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 226 (accept_3_3 5 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  226 2 2 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 142 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 226 2 1 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 142 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 141 226
  (Eq.refl Bool.true) (allA_succ_of_accept 85 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 226 (accept_3_3 83 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 226 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 226 (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 226 (accept_3_3 80 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 141 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 78 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 226 (accept_3_3 77 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 226 (accept_3_3 74 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 226
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 226 (accept_3_3 71 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 226 (accept_3_3 68 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 226 (accept_3_3 65 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 226 (Polychromatic418967fa.accept_14_8_1_2_1_965 64 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 226 (accept_3_3 62 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 226
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 60 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 226 (accept_3_3 59 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 141 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 141 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 226 (accept_3_3 56 141 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 226 (accept_3_3 53 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 226 (accept_3_3 50 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 226 (accept_3_3 47 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 226 (Polychromatic418967fa.accept_13_7_11_5_1_2302 46 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 226 (accept_3_3 44 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 226
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 226 (accept_3_3 41 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 226 (accept_3_3 38 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 226
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 226 (accept_3_3 35 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 226 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 226 (accept_3_3 32 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 226 (accept_3_3 29 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 226 (Polychromatic418967fa.accept_19_9_8_17_1_8053 28 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 226 (accept_3_3 26 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 226
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 226 (accept_3_3 23 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 226 (accept_3_3 20 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 226 (accept_3_3 17 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 226 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 226 (accept_3_3 14 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 226
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 226 (accept_3_3 11 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 226 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 226 (accept_3_3 8 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 226 (accept_3_3 5 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 226 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 226 (accept_3_3 2 141 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 140 226
  (Eq.refl Bool.true) (allA_of_3_1 87 140 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 139 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 139 226 (accept_3_3 86 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 139 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 139 226 (accept_3_3 83 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 139 226 (Polychromatic418967fa.accept_13_4_9_5_1_1641 82 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 226 (accept_3_3 80 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 139 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 226 (accept_3_3 77 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 226 (accept_3_3 74 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 226
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 226 (accept_3_3 71 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 226 (accept_3_3 68 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 226 (accept_3_3 65 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 226 (accept_3_3 62 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 226 (accept_3_3 59 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 226 (Polychromatic418967fa.accept_18_4_13_10_1_2064 58 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 226 (accept_3_3 56 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 226 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 226
  (Polychromatic418967fa.accept_13_2_9_5_1_959 54 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 226 (accept_3_3 53 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 226 (accept_3_3 50 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 226 (accept_3_3 47 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 226 (accept_3_3 44 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 226
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 226 (accept_3_3 41 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 226 (accept_3_3 38 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 226 (accept_3_3 35 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 226 (accept_3_3 32 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 226 (accept_3_3 29 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 226 (accept_3_3 26 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 226 (accept_3_3 23 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 226 (accept_3_3 20 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 226 (Polychromatic418967fa.accept_17_2_3_5_1_763 19 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 226 (accept_3_3 17 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 226 (accept_3_3 14 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 226
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 226 (accept_3_3 11 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 226 (accept_3_3 8 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 226 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 226
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 226 (accept_3_3 5 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 226 (accept_3_3 2 139 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 138 226
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 138 226 2 44 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 138 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 226 2 43 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 226 2 42 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 226 (accept_3_3 83 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 226 2 41 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 226 2 40 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 226 2 39 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 226 (accept_3_3 77 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 226 2 38 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 138 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 226 2 37 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 226 2 36 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 226 (accept_3_3 71 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 226 2 35 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 226 2 34 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 226 2 33 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 226 (accept_3_3 65 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 226 2 32 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 226 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 226 2 31 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 226 2 30 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 226 (accept_3_3 59 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 226 2 29 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 138 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 226 2 28 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 226
  (Polychromatic418967fa.accept_13_3_8_5_1_974 55 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 226 2 27 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 226 (accept_3_3 53 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 226 2 26 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 226 2 25 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 226 2 24 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 226 (accept_3_3 47 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 226 2 23 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 226 2 22 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 226 2 21 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 226 (accept_3_3 41 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 226 2 20 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 226 2 19 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 226
  (Polychromatic418967fa.accept_17_3_2_5_1_2556 37 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 226 2 18 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 226 (accept_3_3 35 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 226 2 17 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 226 2 16 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 226 2 15 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 226 (accept_3_3 29 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 226 2 14 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 138 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 226 2 13 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 226 2 12 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 226 (accept_3_3 23 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 226 2 11 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 138 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 226 2 10 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 226
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 226 2 9 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 226 (accept_3_3 17 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 226 2 8 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 226 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 226 2 7 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 226
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 226 2 6 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 226 (accept_3_3 11 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 226 2 5 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 138 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 226 2 4 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 226
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 226 2 3 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 226 (accept_3_3 5 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  226 2 2 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 226 2 1 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 226 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 138 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 137 226
  (Eq.refl Bool.true) (allA_of_3_1 90 137 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 136 226 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 136 226 2 45 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 136 226 (accept_3_3 89 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 226 2 44 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 226 (Polychromatic418967fa.accept_20_7_16_6_1_7784 87 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 226 2 43 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 226 2 42 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 226 (accept_3_3 83 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 226 2 41 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 226 (Polychromatic418967fa.accept_13_3_6_5_1_2336 81 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 226 2 40 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 226
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 226 2 39 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 226 (accept_3_3 77 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 226 2 38 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 226 2 37 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 226 2 36 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 136 226 (accept_3_3 71 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 226 2 35 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 226 2 34 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 226 2 33 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 226 (accept_3_3 65 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 226 2 32 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 226 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 226 2 31 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 226 2 30 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 226 (accept_3_3 59 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 226 2 29 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 226 2 28 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 226 2 27 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 226 (accept_3_3 53 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 226 2 26 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 226 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 226 2 25 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 226 2 24 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 226 (accept_3_3 47 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 226 2 23 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 226 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 226 2 22 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 226 2 21 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 226 (accept_3_3 41 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 226 2 20 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 226 (Polychromatic418967fa.accept_19_1_3_17_1_1502 39 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 226 2 19 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 226 2 18 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 136 226 (accept_3_3 35 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 226 2 17 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 226 2 16 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 226 2 15 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 226 (accept_3_3 29 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 226 2 14 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 226 2 13 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 226 2 12 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 226 (accept_3_3 23 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 226 2 11 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 226 (Polychromatic418967fa.accept_19_2_3_17_1_5146 21 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 226 2 10 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 226 2 9 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 226 (accept_3_3 17 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 226 2 8 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 136 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 136 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 226 2 7 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 226 2 6 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 136 226 (accept_3_3 11 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 226 2 5 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 136 226 (Polychromatic418967fa.accept_21_9_10_16_1_7327 9 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 226 2 4 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 226 2 3 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 226 (accept_3_3 5 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  226 2 2 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 226 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 136 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 226 2 1 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 136 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 135 226
  (Eq.refl Bool.true) (allA_succ_of_accept 91 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 135 226 (accept_3_3 89 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 135 226 (Polychromatic418967fa.accept_14_4_9_2_1_95 88 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 135 226 (Polychromatic418967fa.accept_17_2_16_5_1_1584 87 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 226 (accept_3_3 86 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 226
  (Polychromatic418967fa.accept_10_4_5_6_1_651 84 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 226 (accept_3_3 83 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 226 (Polychromatic418967fa.accept_25_7_10_1_1_9948 82 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 226 (accept_3_3 80 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 78 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 226 (accept_3_3 77 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 135 226 (Polychromatic418967fa.accept_16_12_7_2_1_4159 76 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 226 (Polychromatic418967fa.accept_11_9_3_6_1_797 75 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 226 (accept_3_3 74 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 226
  (Polychromatic418967fa.accept_17_4_16_5_1_8635 72 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 226 (accept_3_3 71 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 135 226 (Polychromatic418967fa.accept_17_2_16_5_1_1584 70 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 226 (accept_3_3 68 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 226 (accept_3_3 65 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 226 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 226 (accept_3_3 62 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 226
  (Polychromatic418967fa.accept_14_4_9_2_1_95 60 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 226 (accept_3_3 59 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 226 (Polychromatic418967fa.accept_22_14_3_6_1_10517 58 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 226 (accept_3_3 56 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 226
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 226 (accept_3_3 53 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 226 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 226 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 226 (accept_3_3 50 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 226
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 226 (accept_3_3 47 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 226 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 135 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 226 (accept_3_3 44 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 226
  (Polychromatic418967fa.accept_11_9_3_6_1_797 42 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 226 (accept_3_3 41 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 226 (Polychromatic418967fa.accept_22_18_3_6_1_13512 40 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 226 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 226 (accept_3_3 38 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 226
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 36 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 226 (accept_3_3 35 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 226 (accept_3_3 32 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 226
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 226 (accept_3_3 29 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 226 (Polychromatic418967fa.accept_16_12_7_2_1_4159 28 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 226 (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 226 (accept_3_3 26 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 226
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 226 (accept_3_3 23 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 226 (Polychromatic418967fa.accept_19_3_2_17_1_6574 22 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 226 (accept_3_3 20 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 226 (accept_3_3 17 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 226 (Polychromatic418967fa.accept_19_16_2_17_1_8049 16 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 226 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 226 (accept_3_3 14 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 226
  (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 226 (accept_3_3 11 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 226 (Polychromatic418967fa.accept_19_10_2_17_1_675 10 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 226 (accept_3_3 8 135 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 226
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 226 (accept_3_3 5 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 226 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 226 (Polychromatic418967fa.accept_19_3_2_17_1_6574 3 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 226 (accept_3_3 2 135 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 134 226
  (Eq.refl Bool.true) (allA_of_3_1 93 134 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 133 226 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 133 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 133 226 (accept_3_3 92 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 133 226
  (Polychromatic418967fa.accept_21_6_7_16_1_9035 90 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 133 226 (accept_3_3 89 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 133 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 226 (accept_3_3 86 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 226
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 226 (accept_3_3 83 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 226 (Polychromatic418967fa.accept_11_5_1_6_1_774 82 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 226 (accept_3_3 80 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 226
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 226 (accept_3_3 77 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 226 (accept_3_3 74 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 226 (Polychromatic418967fa.accept_11_7_1_6_1_1281 73 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 226
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 133 226 (accept_3_3 71 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 133 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 69
  133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 226 (accept_3_3 68
  133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 133 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 133 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 226 (accept_3_3 65 133 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 133 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 226 (accept_3_3 62 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 226 (Polychromatic418967fa.accept_13_9_3_5_1_1605 61 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 226 (accept_3_3 59 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 226 (accept_3_3 56 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 226 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 226 (accept_3_3 53 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 226 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 133
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 226 (accept_3_3 50 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 226 (accept_3_3 47 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 226 (Polychromatic418967fa.accept_21_4_7_16_1_2938 46 133 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 226 (accept_3_3 44 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 226 (accept_3_3 41 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 226 (accept_3_3 38 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 226 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 226 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 226 (accept_3_3 35 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 226 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 133
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 226 (accept_3_3 32 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 226 (accept_3_3 29 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 226 (accept_3_3 26 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 226 (accept_3_3 23 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 226 (accept_3_3 20 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 226 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 226 (accept_3_3 17 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 226 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 133
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 226 (accept_3_3 14 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 226 (accept_3_3 11 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 226 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 133 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 226 (accept_3_3 8 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 226 (accept_3_3 5 133 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 226 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 226
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 226 (accept_3_3 2 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 226 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 133 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 132
  226 (Eq.refl Bool.true) (allA_succ_of_gcd 94 132 226 2 47 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 132 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 132 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 226 2 46 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 226
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 226 2 45 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 226 (accept_3_3 89 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 226 2 44 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 132 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 226 2 43 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 226 2 42 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 226 (accept_3_3 83 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 226 2 41 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 226 2 40 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 226 2 39 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 226 (accept_3_3 77 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 226 2 38 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 226 2 37 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 226 2 36 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 226 (accept_3_3 71 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 226 2 35 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 226 (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 132 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 226 2 34 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 226 2 33 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 226 (accept_3_3 65 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 226 2 32 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 226 (Polychromatic418967fa.accept_19_6_18_17_1_9518 63 132 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 226 2 31 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 226 2 30 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 226 (accept_3_3 59 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 226 2 29 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 226 2 28 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 226
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 55 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 226 2 27 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 226 (accept_3_3 53 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 226 2 26 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 226 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 226 2 25 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 226 2 24 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 226 (accept_3_3 47 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 226 2 23 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 226 2 22 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 226
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 226 2 21 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 226 (accept_3_3 41 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 226 2 20 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 226 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 226 2 19 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 226
  (Polychromatic418967fa.accept_20_17_12_6_1_6171 37 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 132 226 2 18 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 132 226 (accept_3_3 35 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 226 2 17 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 132 226 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 132 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 226 2 16 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 226
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 226 2 15 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 226 (accept_3_3 29 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 226 2 14 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 226 (Polychromatic418967fa.accept_17_10_13_5_1_3513 27 132 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 226 2 13 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 226
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 226 2 12 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 226 (accept_3_3 23 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 226 2 11 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 132 226 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 226 2 10 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 226
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 226 2 9 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 226 (accept_3_3 17 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 226 2 8 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 132 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 226 2 7 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 226
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 226 2 6 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 226 (accept_3_3 11 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 226 2 5 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 132 226 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 132 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 226 2 4 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 226
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 226 2 3 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 226 (accept_3_3 5 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132
  226 2 2 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  132 226 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 132 226 2 1 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 132 226 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 131
  226 (Eq.refl Bool.true) (allA_of_3_1 96 131 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 130 226
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 130 226 2 48 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 130 226 (accept_3_3 95 130 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 130 226 2 47 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 130 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 130 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 226 2 46 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 130 226
  (Polychromatic418967fa.accept_11_3_9_6_1_105 91 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 130 226 2 45 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 130 226 (accept_3_3 89 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 130 226 2 44 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 87 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 226 2 43 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 130 226
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 85 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 130 226 2 42 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 130 226 (accept_3_3 83 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 226 2 41 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 226 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 130 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 226 2 40 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 226 2 39 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 226 (accept_3_3 77 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 226 2 38 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 226 2 37 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 226
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 130 226 2 36 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 130 226 (accept_3_3 71 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 226 2 35 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 226 2 34 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 226
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 226 2 33 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 226 (accept_3_3 65 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 226 2 32 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 226 (Polychromatic418967fa.accept_22_19_20_6_1_8814 63 130 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 226 2 31 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 226 2 30 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 226 (accept_3_3 59 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 226 2 29 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 226 2 28 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 226 2 27 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 226 (accept_3_3 53 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 226 2 26 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 226 2 25 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 226
  (Polychromatic418967fa.accept_17_15_11_5_1_9866 49 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 130 226 2 24 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 130 226 (accept_3_3 47 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 226 2 23 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 226 (Polychromatic418967fa.accept_19_7_16_17_1_6567 45 130 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 226 2 22 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 226 2 21 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 226 (accept_3_3 41 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 226 2 20 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 226 2 19 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 226
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 226 2 18 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 226 (accept_3_3 35 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 226 2 17 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 226 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 226 2 16 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 226
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 31 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 226 2 15 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 226 (accept_3_3 29 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 226 2 14 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 226 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 226 2 13 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 226 2 12 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 226 (accept_3_3 23 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 226 2 11 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 226 2 10 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 226
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 226 2 9 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 226 (accept_3_3 17 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 226 2 8 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 226 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 226 2 7 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 226
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 226 2 6 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 130 226 (accept_3_3 11 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 226 2 5 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 226 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 130 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 226 2 4 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 226
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 226 2 3 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 226 (accept_3_3 5 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  226 2 2 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 226 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 130 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 226 2 1 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 226 (Polychromatic418967fa.accept_19_1_16_17_1_3864 1 130 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  129 226 (Eq.refl Bool.true) (allA_succ_of_accept 97 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 96 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 129 226 (accept_3_3 95 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 129 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 129 226 (Polychromatic418967fa.accept_10_3_9_6_1_94 93 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 226 (accept_3_3 92 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 90 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 129 226 (accept_3_3 89 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 129 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 226 (accept_3_3 86 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 226
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 84 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 226 (accept_3_3 83 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 226 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 226 (accept_3_3 80 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 129 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 78 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 226 (accept_3_3 77 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 226 (accept_3_3 74 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 226
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 226 (accept_3_3 71 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 129 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 226 (accept_3_3 68 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 66 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 226 (accept_3_3 65 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 226 (accept_3_3 62 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 226 (accept_3_3 59 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 226 (accept_3_3 56 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 226 (accept_3_3 53 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 226 (accept_3_3 50 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 226 (accept_3_3 47 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 226 (Polychromatic418967fa.accept_13_7_12_5_1_1603 46 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 226 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 226 (accept_3_3 44 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 226 (accept_3_3 41 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 226 (accept_3_3 38 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 226
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 226 (accept_3_3 35 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 226 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 226 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 226 (accept_3_3 32 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 226 (accept_3_3 29 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 226 (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 226 (accept_3_3 26 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 226
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 226 (accept_3_3 23 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 226 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 226 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 226 (accept_3_3 20 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 226
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 226 (accept_3_3 17 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 226 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 226 (accept_3_3 14 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 226
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 226 (accept_3_3 11 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 226 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 226 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 226 (accept_3_3 8 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 226
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 226 (accept_3_3 5 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 226 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 129 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 226 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 226 (accept_3_3 2 129 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 226 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  128 226 (Eq.refl Bool.true) (allA_of_3_1 99 128 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 127 226
  (Eq.refl Bool.true) (allA_succ_of_accept 99 127 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 226 (accept_3_3 98 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 226
  (Polychromatic418967fa.accept_15_6_7_1_1_93 96 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 226 (accept_3_3 95 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 94 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 226 (accept_3_3 92 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 226 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 226
  (Polychromatic418967fa.accept_7_6_1_2_1_230 90 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 127 226 (accept_3_3 89 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 127 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 226 (accept_3_3 86 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 226
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 84 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 226 (accept_3_3 83 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 226 (Polychromatic418967fa.accept_13_4_10_5_1_1644 82 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 226 (accept_3_3 80 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 226 (Polychromatic418967fa.accept_20_19_7_6_1_6255 79 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 226
  (Polychromatic418967fa.accept_14_8_1_2_1_965 78 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 226 (accept_3_3 77 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 226 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 226 (accept_3_3 74 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 226
  (Polychromatic418967fa.accept_19_15_13_17_1_5172 72 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 127 226 (accept_3_3 71 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 127 226 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 127 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 226 (accept_3_3 68 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 226
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 67 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 127 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 226 (accept_3_3 65 127 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 226 (accept_3_3 62 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 226 (Polychromatic418967fa.accept_13_8_10_5_1_977 60 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 226 (accept_3_3 59 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 226 (Polychromatic418967fa.accept_13_6_10_5_1_1648 58 127
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 226 (accept_3_3 56 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 226 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 226 (accept_3_3 53 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 226 (accept_3_3 50 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 226 (accept_3_3 47 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 226 (Polychromatic418967fa.accept_17_12_8_5_1_6018 46 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 226 (accept_3_3 44 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 226 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 226 (Polychromatic418967fa.accept_19_4_13_17_1_5137 42 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 226 (accept_3_3 41 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 127
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 226 (accept_3_3 38 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 226 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 226 (accept_3_3 35 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 226 (accept_3_3 32 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 226 (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 226 (accept_3_3 29 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 127
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 226 (accept_3_3 26 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 226 (accept_3_3 23 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 226 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 226 (accept_3_3 20 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 226 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 226 (Polychromatic418967fa.accept_19_18_13_17_1_9517 18 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 226 (accept_3_3 17 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 127
  226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 226 (accept_3_3 14 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 226 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 226 (accept_3_3 11 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 226 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 226
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 226 (accept_3_3 8 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 226 (Polychromatic418967fa.accept_19_7_13_17_1_8041 7 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 226 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 226 (accept_3_3 5 127 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 226 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 127 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 226
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 226 (accept_3_3 2 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 226 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 126 226 (Eq.refl Bool.true) (allA_succ_of_gcd 100 126 226 2 50 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576
  99 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 126 226 2 49 63 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 226
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 226 2 48 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 226 (accept_3_3 95 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 126 226 2 47 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 93 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 226 2 46 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 226
  (Polychromatic418967fa.accept_19_15_12_17_1_5195 91 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 126 226 2 45 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 126 226 (accept_3_3 89 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 126 226 2 44 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 126 226 (Polychromatic418967fa.accept_11_10_5_6_1_1842 87 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 226 2 43 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 226
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 85 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 226 2 42 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 226 (accept_3_3 83 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 226 2 41 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 226 2 40 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 226
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 79 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 226 2 39 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 226 (accept_3_3 77 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 226 2 38 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 226 2 37 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 226
  (Polychromatic418967fa.accept_26_21_22_18_1_13511 73 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 126 226 2 36 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 126 226 (accept_3_3 71 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 226 2 35 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 226 2 34 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 226
  (Polychromatic418967fa.accept_11_1_5_6_1_397 67 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 226 2 33 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 226 (accept_3_3 65 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 226 2 32 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 226 2 31 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 226
  (Polychromatic418967fa.accept_23_15_11_19_1_11854 61 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 226 2 30 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 226 (accept_3_3 59 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 226 2 29 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 226 2 28 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 226
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 55 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 226 2 27 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 226 (accept_3_3 53 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 226 2 26 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 226 2 25 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 226
  (Polychromatic418967fa.accept_17_15_7_5_1_9836 49 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 226 2 24 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 226 (accept_3_3 47 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 226 2 23 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 226 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 126 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 226 2 22 63 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 226
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 226 2 21 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 226 (accept_3_3 41 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 226 2 20 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 226 2 19 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 226
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 226 2 18 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 226 (accept_3_3 35 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 226 2 17 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 226 2 16 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 226
  (Polychromatic418967fa.accept_22_9_16_6_1_2493 31 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 226 2 15 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 226 (accept_3_3 29 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 226 2 14 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 226 2 13 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 226
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 226 2 12 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 226 (accept_3_3 23 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 226 2 11 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 226 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 226 2 10 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 226
  (Polychromatic418967fa.accept_27_19_18_10_1_13510 19 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 226 2 9 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 226 (accept_3_3 17 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 226 2 8 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 226 2 7 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 226
  (Polychromatic418967fa.accept_22_13_16_6_1_8823 13 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 226 2 6 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 226 (accept_3_3 11 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 226 2 5 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 226 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 226 2 4 63 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 226
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 226 2 3 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 226 (accept_3_3 5 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  226 2 2 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 226 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 226 2 1 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 226 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 126 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  226))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 125 226 (Eq.refl Bool.true) (allA_of_3_1 102 125 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 124
  226 (Eq.refl Bool.true) (allA_succ_of_gcd 102 124 226 2 51 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 124 226 (accept_3_3 101 124 226 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 124 226 2 50 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 124 226 (Polychromatic418967fa.accept_19_4_10_17_1_5194 99 124 226
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 226 2 49 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 226
  (Polychromatic418967fa.accept_11_9_3_6_1_797 97 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 124 226 2 48 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 124 226 (accept_3_3 95 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 226 2 47 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 226 2 46 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 91 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 124 226 2 45 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 124 226 (accept_3_3 89 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 226 2 44 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 226 2 43 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 85 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 226 2 42 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 226 (accept_3_3 83 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 226 2 41 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 226 2 40 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 226 2 39 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 226 (accept_3_3 77 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 226 2 38 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 226 2 37 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 226 2 36 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 226 (accept_3_3 71 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 226 2 35 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 226 2 34 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 226 2 33 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 226 (accept_3_3 65 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 226 2 32 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 226 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 124 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 226 2 31 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 226 2 30 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 226 (accept_3_3 59 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 226 2 29 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 226 2 28 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 226
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 226 2 27 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 226 (accept_3_3 53 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 226 2 26 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 226 2 25 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 226 2 24 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 226 (accept_3_3 47 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 226 2 23 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 226 2 22 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 226 2 21 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 226 (accept_3_3 41 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 226 2 20 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 226 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 226 2 19 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 226
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 226 2 18 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 226 (accept_3_3 35 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 226 2 17 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 226 2 16 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 226
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 226 2 15 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 226 (accept_3_3 29 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 226 2 14 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 226 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 124 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 226 2 13 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 226
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 226 2 12 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 226 (accept_3_3 23 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 226 2 11 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 226 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 226 2 10 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 226
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 226 2 9 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 226 (accept_3_3 17 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 226 2 8 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 124 226 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 226 2 7 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 226
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 226 2 6 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 124 226 (accept_3_3 11 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 226 2 5 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 124 226 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 124 226 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 226 2 4 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 226
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 226 2 3 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 226 (accept_3_3 5 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  226 2 2 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 226 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 226 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 226 2 1 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 124 226 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 124 226 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  226)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_226_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


