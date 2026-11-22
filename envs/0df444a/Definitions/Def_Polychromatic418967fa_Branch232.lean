-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch232
-- name    : Polychromatic418967fa_Branch232
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:21.654786+00:00
-- url     : https://prove2.me/theorems/c55748cc-b977-4005-adf4-13b3c8708197
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch232_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_232 : allB 232 232 :=
  allB_succ' 2 231 232 (Eq.refl Bool.true) (allA_succ_of_accept 1 231 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  231 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 232)) (allB_succ' 3 230 232
  (Eq.refl Bool.true) (allA_of_3_1 3 230 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 229 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 229 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 229 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 232 (accept_3_3 2 229 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 229 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 232)))) (allB_succ' 5 228 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 228 232 4 1 57 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 228 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 228 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 232 2 1 114 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 228
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 232))))) (allB_succ' 6 227 232 (Eq.refl
  Bool.true) (allA_of_3_1 6 227 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 226 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 226 232 2 3 113 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 232 (accept_3_3 5 226 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 232 2 2 113 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 226 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 232 2 1 113 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 226 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 232))))))) (allB_succ' 8 225 232 (Eq.refl Bool.true) (allA_succ_of_accept 7 225 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 225 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 225 232 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 225 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 232 (accept_3_3 5 225 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 225 232 (Polychromatic418967fa.accept_16_4_1_8_1_835 4 225 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  225 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 232 (accept_3_3 2 225
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 225 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 232)))))))) (allB_succ' 9 224 232
  (Eq.refl Bool.true) (allA_of_3_1 9 224 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 223 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 223 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 223 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 232 (accept_3_3 8 223 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 232 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 223 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 232
  (Polychromatic418967fa.accept_15_6_13_7_1_222 6 223 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 232 (accept_3_3 5 223 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 232 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 223 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 232 (accept_3_3 2 223 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 223 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 232)))))))))) (allB_succ' 11 222 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 222 232 2 5 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 222 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 222 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 232 2 4 111 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 232
  (Polychromatic418967fa.accept_13_7_1_11_1_732 7 222 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 232 2 3 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 232 (accept_3_3 5 222 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 232 2 2 111 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 222 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 232 2 1 111 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 222 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 232))))))))))) (allB_succ' 12 221 232 (Eq.refl Bool.true) (allA_of_3_1 12 221 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 220 232 (Eq.refl Bool.true) (allA_succ_of_gcd 12 220 232 4 3 55 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 220 232 (accept_3_3 11
  220 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 232 2 5 110 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 220 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 220 232 4 2 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 220 232 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 220 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 232 2 3 110 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 232 (accept_3_3 5 220 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 232 4 1 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 220 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 220 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 232 2 1 110 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 220 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 232))))))))))))) (allB_succ' 14 219 232 (Eq.refl Bool.true) (allA_succ_of_accept 13 219 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 219 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 219 232 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 219 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 232 (accept_3_3 11 219 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 219 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 232 (Polychromatic418967fa.accept_11_9_10_1_1_581
  9 219 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 232 (accept_3_3 8
  219 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 219 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 219 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 219 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 232 (accept_3_3 5 219 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 219 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 219 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  219 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 232 (accept_3_3 2 219
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 219 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 232)))))))))))))) (allB_succ' 15
  218 232 (Eq.refl Bool.true) (allA_of_3_1 15 218 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 217 232
  (Eq.refl Bool.true) (allA_succ_of_accept 15 217 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 217 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 232 (accept_3_3 14 217 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 232 (accept_3_3 11 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 232 (accept_3_3 8 217 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 232 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 217 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 232 (accept_3_3 5 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 232 (accept_3_3 2 217 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 232 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 217 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 232)))))))))))))))) (allB_succ' 17 216 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 16 216 232 8 2 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 216 232 (Polychromatic418967fa.accept_21_15_6_1_1_6306 15 216 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 232 2 7 108 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 232
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 216 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 232 4 3 54 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 232 (accept_3_3 11 216 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  216 232 2 5 108 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 216 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 216 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 232 8 1 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 232 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 216 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 232 2 3 108 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 232 (accept_3_3 5
  216 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 232 4 1 54 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 232
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 216 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 232 2 1 108 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 216 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 232))))))))))))))))) (allB_succ' 18 215 232 (Eq.refl Bool.true)
  (allA_of_3_1 18 215 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 214 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 214 232 2 9 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 232 (accept_3_3 17 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 232 2 8 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 232 (Polychromatic418967fa.accept_19_15_5_4_1_1867 15 214 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 232 2 7 107 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 232 2 6 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 232 (accept_3_3 11 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 232 2 5 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 232 (Polychromatic418967fa.accept_19_9_5_4_1_1866 9 214 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 232 2 4 107 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 232 2 3 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 232 (accept_3_3 5 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 232 2 2 107 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 214 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 232 2 1 107 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 214 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 232))))))))))))))))))) (allB_succ' 20 213 232 (Eq.refl Bool.true) (allA_succ_of_accept 19 213 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 213 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 213 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 232 (accept_3_3 17 213 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 213 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 213 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 232 (Polychromatic418967fa.accept_10_5_3_2_1_899
  15 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 232 (accept_3_3 14
  213 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 213 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 213 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 232 (accept_3_3 11 213 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 213 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 213 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 232 (accept_3_3 8 213
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 232 (accept_3_3 5 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 213 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 232 (accept_3_3 2 213 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 232)))))))))))))))))))) (allB_succ' 21 212 232
  (Eq.refl Bool.true) (allA_of_3_1 21 212 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 211 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 211 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 232 (accept_3_3 20 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 211 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 232
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 232 (accept_3_3 17 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 232 (accept_3_3 14 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 211 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 232 (accept_3_3 11 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 232 (accept_3_3 8 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 232 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 211 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 232 (accept_3_3 5 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 232 (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 211 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 232 (accept_3_3 2 211 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 211 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 232)))))))))))))))))))))) (allB_succ' 23 210 232
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 210 232 2 11 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 210 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 232 2 10 105 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 232 2 9 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 232 (accept_3_3 17 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 232 2 8 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 210 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 210 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 232 2 7 105 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 232 2 6 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 232 (accept_3_3 11 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 232 2 5 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 232 2 4 105 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 232
  (Polychromatic418967fa.accept_19_7_1_4_1_12606 7 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 232 2 3 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 232 (accept_3_3 5 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 232 2 2 105 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 210 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 232 2 1 105 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 232))))))))))))))))))))))) (allB_succ' 24 209 232 (Eq.refl Bool.true) (allA_of_3_1 24 209 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 208 232 (Eq.refl Bool.true) (allA_succ_of_gcd 24 208 232 8 3 26 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 232
  (accept_3_3 23 208 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 232 2 11 104 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 208 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 208 232 4 5 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 208 232 (Polychromatic418967fa.accept_18_1_10_16_1_566 19 208 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 208 232 2 9 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 208 232 (accept_3_3 17 208 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 208 232 8 2 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 208 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 208 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 232 2 7 104 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 208 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 232 4 3 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 208 232 (accept_3_3 11 208 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  208 232 2 5 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 208 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 208 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 232 8 1 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 232 (Polychromatic418967fa.accept_21_7_19_1_1_9497 7 208 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 232 2 3 104 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 232 (accept_3_3 5
  208 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 232 4 1 52 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 208 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 232 2 1 104 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 232 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 208 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 232))))))))))))))))))))))))) (allB_succ' 26 207 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 207 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 232 (accept_3_3 23
  207 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 232
  (Polychromatic418967fa.accept_20_2_7_12_1_5215 22 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 207 232 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 207 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 232 (accept_3_3 20 207 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 207 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 232 (Polychromatic418967fa.accept_12_6_3_4_1_394
  18 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 232 (accept_3_3 17
  207 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 232
  (Polychromatic418967fa.accept_26_16_25_24_1_13886 16 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 207 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 232 (accept_3_3 14 207 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 232 (accept_3_3 11 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 232 (accept_3_3 8 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 232 (accept_3_3 5 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 207 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 232 (accept_3_3 2 207 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207 232)))))))))))))))))))))))))) (allB_succ' 27 206 232
  (Eq.refl Bool.true) (allA_of_3_1 27 206 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 205 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 205 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 232 (accept_3_3 26 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 232 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 205 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 232 (accept_3_3 23 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 232 (accept_3_3 20 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 232 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 205 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 232
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 232 (accept_3_3 17 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 232 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 232 (accept_3_3 14 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 205 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 232
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 205 232 (accept_3_3 11 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 205 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 205 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 232 (accept_3_3 8 205 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 7
  205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 232 (accept_3_3 5 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 232 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 205 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 232 (accept_3_3 2 205 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 232 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 205 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 232)))))))))))))))))))))))))))) (allB_succ' 29 204
  232 (Eq.refl Bool.true) (allA_succ_of_gcd 28 204 232 4 7 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 204 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 232 2 13 102 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 232
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 232 4 6 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 204 232 (accept_3_3 23 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  204 232 2 11 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 204 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 204 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 232 4 5 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 232 2 9 102 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 232 (accept_3_3 17
  204 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 232 4 4 51 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 232
  (Polychromatic418967fa.accept_13_2_9_11_1_258 15 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 204 232 2 7 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 204 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 232 4 3 51 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 232 (accept_3_3 11 204 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 232 2 5 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 232 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  9 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 232 4 2 51 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 232 2 3 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 232 (accept_3_3 5 204 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 232 4 1 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 204 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 204 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 232 2 1 102 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  204 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 232)))))))))))))))))))))))))))))
  (allB_succ' 30 203 232 (Eq.refl Bool.true) (allA_of_3_1 30 203 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 202 232 (Eq.refl Bool.true) (allA_succ_of_gcd 30 202 232 2 15 101 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 202 232 (accept_3_3 29 202 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 202 232 2 14 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 202 232 (Polychromatic418967fa.accept_13_1_7_11_1_702
  27 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 232 2 13 101 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 232 2 12 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 232 (accept_3_3 23 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 232 2 11 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 202 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 232 2 10 101 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 232 2 9 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 232 (accept_3_3 17 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 232 2 8 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 202 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 232 2 7 101 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 232 2 6 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 232 (accept_3_3 11 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 232 2 5 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 202 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 232 2 4 101 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 232 2 3 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 232 (accept_3_3 5 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 232 2 2 101 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 202 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 232 2 1 101 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 202 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 232))))))))))))))))))))))))))))))) (allB_succ' 32 201 232 (Eq.refl Bool.true) (allA_succ_of_accept 31
  201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 232 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 232 (accept_3_3 29 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 232 (accept_3_3 26 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 232 (accept_3_3 23 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 232
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 232 (accept_3_3 20 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 232 (accept_3_3 17 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 232 (accept_3_3 14 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 232 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 232 (accept_3_3 11 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 201 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 232
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 232 (accept_3_3 8 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 232 (accept_3_3 5 201 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 201 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 232 (accept_3_3 2 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 232)))))))))))))))))))))))))))))))) (allB_succ' 33 200 232 (Eq.refl Bool.true) (allA_of_3_1
  33 200 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 199 232 (Eq.refl Bool.true) (allA_succ_of_accept 33
  199 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 199 232 (accept_3_3 32 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 199 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 199 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 232 (accept_3_3 29 199 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 232
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 199 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 232 (accept_3_3 26 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 199 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 199 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 232 (Polychromatic418967fa.accept_9_6_1_7_1_577
  24 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 232 (accept_3_3 23
  199 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 199 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 232 (accept_3_3 20 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 199 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 199 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 232 (accept_3_3 17
  199 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 199 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 232 (accept_3_3 14 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 199 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 199 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 232 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 232 (accept_3_3 11
  199 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 232
  (Polychromatic418967fa.accept_12_10_7_4_1_820 10 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 199 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 232 (accept_3_3 8 199 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 199 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 199 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 232 (accept_3_3 5 199
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 232 (Polychromatic418967fa.accept_7_4_3_1_1_87
  4 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 232 (accept_3_3 2 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 199 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 232)))))))))))))))))))))))))))))))))) (allB_succ' 35 198 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 198 232 2 17 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 198 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 198 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 198 232 2 16 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 232 2 15 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 232 (accept_3_3 29 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 232 2 14 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 198 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 232 2 13 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 232
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 232 2 12 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 232 (accept_3_3 23 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 198 232 2 11 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 198 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 232 2 10 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 232
  (Polychromatic418967fa.accept_15_4_3_7_1_713 19 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 232 2 9 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 232 (accept_3_3 17 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 232 2 8 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 198 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 232 2 7 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 232 2 6 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 232 (accept_3_3 11 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 232 2 5 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 198 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 232 2 4 99 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 232
  (Polychromatic418967fa.accept_13_7_3_11_1_280 7 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 232 2 3 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 232 (accept_3_3 5 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  232 2 2 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 198 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 232 2 1 99 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 232 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 198 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 232))))))))))))))))))))))))))))))))))) (allB_succ'
  36 197 232 (Eq.refl Bool.true) (allA_of_3_1 36 197 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 196 232
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 196 232 4 9 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 196 232 (accept_3_3 35 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 196 232 2 17 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 196 232 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 196 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 232 4 8 49 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 196 232 2 15 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 196 232 (accept_3_3 29 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 196 232 4 7 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 196 232 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 196 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 232 2 13 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 232
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 196 232 4 6 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 196 232 (accept_3_3 23 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 196 232 2 11 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 196 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 196 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 232 4 5 49 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 232
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 196 232 2 9 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 196 232 (accept_3_3 17 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 232 4 4 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 196 232 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 196 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 232 2 7 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 232 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 232 4 3 49 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 232
  (accept_3_3 11 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 232 2 5 98 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 232
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 196 232 4 2 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 196 232 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 196 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 232 2 3 98 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 232 (accept_3_3 5 196 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 232 4 1 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 196 232 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 196 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 232 2 1 98 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 196 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 232))))))))))))))))))))))))))))))))))))) (allB_succ' 38 195 232 (Eq.refl Bool.true) (allA_succ_of_accept
  37 195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 232 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 232 (accept_3_3 35 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 232 (Polychromatic418967fa.accept_19_15_5_4_1_1867 34 195
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 232 (accept_3_3 32 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 232 (accept_3_3 29 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 232
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 232 (accept_3_3 26 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 232 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 232 (accept_3_3 23 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 195 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 232 (accept_3_3 20 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 232 (accept_3_3 17 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 195 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 232
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 232 (accept_3_3 14 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 195 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 232 (accept_3_3 11 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 232 (accept_3_3 8 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 232 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 232 (accept_3_3 5 195 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 195 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 232 (accept_3_3 2 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 195 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 232)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 194 232 (Eq.refl Bool.true)
  (allA_of_3_1 39 194 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 193 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 232 (accept_3_3 38 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 193 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 232 (Polychromatic418967fa.accept_15_6_13_7_1_222
  36 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 232 (accept_3_3 35
  193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 232
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 232 (accept_3_3 32 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 193 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 30
  193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 232 (accept_3_3 29
  193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 232 (accept_3_3 26 193 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 193 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 193 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 232 (accept_3_3 23 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 232 (accept_3_3 20 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 193 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 232
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 232 (accept_3_3 17 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 232 (accept_3_3 14 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 232 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 193 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 232 (accept_3_3 11 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 232 (accept_3_3 8 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 232 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 193 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 232 (accept_3_3 5 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 232 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 193 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 232 (accept_3_3 2 193 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 232))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 192 232 (Eq.refl Bool.true) (allA_succ_of_gcd 40 192 232 8 5 24 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 232 2 19 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 192 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 232 4 9 48 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 232 (accept_3_3 35 192 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 232 2 17 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 232 8 4 24 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 232 2 15 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 232 (accept_3_3 29 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 232 4 7 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 192 232 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 192 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 232 2 13 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 232 8 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 232 (accept_3_3 23 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  192 232 2 11 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 192 232 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 192 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 232 4 5 48 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 232 2 9 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 232 (accept_3_3 17 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 232 8 2 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 192 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 192 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 232 2 7 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 232 4 3 48 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 232 (accept_3_3 11
  192 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 232 2 5 96 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 232 8 1 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 232 (Polychromatic418967fa.accept_17_7_5_11_1_2922 7 192 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 232 2 3 96 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 232 (accept_3_3 5 192 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 232 4 1 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 232 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 192 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 232 2 1 96 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 192 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 232))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 191 232 (Eq.refl Bool.true) (allA_of_3_1 42
  191 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 190 232 (Eq.refl Bool.true) (allA_succ_of_gcd 42 190
  232 2 21 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 190 232 (accept_3_3 41 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 190 232 2 20 95 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 190 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 190 232 2 19 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 190 232 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 190 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 190 232 2 18 95 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 190 232 (accept_3_3 35 190 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 190 232 2 17 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 190 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 190 232 2 16 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 190 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 190 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 232 2 15 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 232 (accept_3_3 29 190 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 190 232 2 14 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 190 232 (Polychromatic418967fa.accept_13_1_8_11_1_724
  27 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 232 2 13 95 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 232 2 12 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 232 (accept_3_3 23 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 232 2 11 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 190 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 232 2 10 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 232 2 9 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 232 (accept_3_3 17 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 232 2 8 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 190 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 232 2 7 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 232 2 6 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 232 (accept_3_3 11 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 232 2 5 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 232 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 190 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 232 2 4 95 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 232 2 3 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 232 (accept_3_3 5 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  232 2 2 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 190 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 232 2 1 95 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 232 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 190 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 232)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 189 232 (Eq.refl Bool.true) (allA_succ_of_accept 43 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 189 232 (accept_3_3 41 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 189 232 (Polychromatic418967fa.accept_13_1_7_11_1_702 40 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 189 232 (Polychromatic418967fa.accept_20_19_9_12_1_9740 39 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 232 (accept_3_3 38 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 232
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 189 232 (accept_3_3 35 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 189 232 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 189 232 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 232 (accept_3_3 32 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 189 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 189 232 (accept_3_3 29 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 189 232 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 189 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 232 (accept_3_3 26 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 232
  (Polychromatic418967fa.accept_19_5_18_4_1_2956 24 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 232 (accept_3_3 23 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 232 (Polychromatic418967fa.accept_13_9_7_11_1_1292 22 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 189 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 232 (accept_3_3 20 189 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 232 (accept_3_3 17 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 232 (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 189 232 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 232 (accept_3_3 14 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 232
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 232 (accept_3_3 11 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 232 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 189 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 232 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 189
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 232 (accept_3_3 8 189 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 232 (accept_3_3 5 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 232 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 189 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 232 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 189 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 232 (accept_3_3 2 189 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 232))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 188 232 (Eq.refl Bool.true) (allA_of_3_1 45 188 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 187 232 (Eq.refl Bool.true) (allA_succ_of_accept 45 187 232 (Polychromatic418967fa.accept_6_3_1_4_1_25
  45 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 232 (accept_3_3 44
  187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 232
  (Polychromatic418967fa.accept_22_21_11_12_1_10810 43 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 187 232 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 232 (accept_3_3 41 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 232 (Polychromatic418967fa.accept_18_4_7_16_1_2307 40 187
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 232 (accept_3_3 38 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 232 (Polychromatic418967fa.accept_16_5_11_8_1_3431 37 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 232 (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 232 (accept_3_3 35 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 187 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 232 (accept_3_3 32 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 232 (Polychromatic418967fa.accept_19_11_16_4_1_7075 30 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 232 (accept_3_3 29 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 232 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 187
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 232 (accept_3_3 26 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 232 (accept_3_3 23 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 232 (accept_3_3 20 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 232 (accept_3_3 17 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 232 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 232 (accept_3_3 14 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 232 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 232 (accept_3_3 11 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 187 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 232 (accept_3_3 8 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 232 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 232 (accept_3_3 5 187 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 187 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 232 (accept_3_3 2 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 232 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 187 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 232)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 186 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 186 232 2 23 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 232 2 22 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 232
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 232 2 21 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 232 (accept_3_3 41 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 232 2 20 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 232 2 19 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 232 2 18 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 232 (accept_3_3 35 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 232 2 17 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 232 2 16 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 232 2 15 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 232 (accept_3_3 29 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 232 2 14 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 232 2 13 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 232
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 186 232 2 12 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 186 232 (accept_3_3 23 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 232 2 11 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 232 2 10 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 232 2 9 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 232 (accept_3_3 17 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 232 2 8 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 232 2 7 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 232 2 6 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 232 (accept_3_3 11 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 232 2 5 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 186 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 232 2 4 93 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 232
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 232 2 3 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 232 (accept_3_3 5 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  232 2 2 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 232 2 1 93 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 232)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 185 232 (Eq.refl Bool.true) (allA_of_3_1 48 185 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 184 232 (Eq.refl Bool.true) (allA_succ_of_gcd 48 184 232 8 6 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 184 232 (accept_3_3 47 184 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 184 232 2 23 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 184 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 45
  184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 232 4 11 46 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 232
  (Polychromatic418967fa.accept_13_4_2_11_1_733 43 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 184 232 2 21 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 184 232 (accept_3_3 41 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 184 232 8 5 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 184 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 184 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 232 2 19 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 37
  184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 232 4 9 46 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 232 (accept_3_3 35
  184 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 232 2 17 92 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 184 232 8 4 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 184 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 184 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 232 2 15 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 232 (accept_3_3 29 184 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 232 4 7 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 184 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 232 2 13 92 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 232
  (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 232 8 3 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 184 232 (accept_3_3 23 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  184 232 2 11 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 184 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 184 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 232 4 5 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 19
  184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 232 2 9 92 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 232 (accept_3_3 17
  184 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 232 8 2 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 184 232 2 7 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 184 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 184 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 232 4 3 46 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 232 (accept_3_3 11 184 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 232 2 5 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 232 (Polychromatic418967fa.accept_13_9_2_11_1_1964
  9 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 232 8 1 23 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 232 2 3 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 232 (accept_3_3 5 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  232 4 1 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 184 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 232 2 1 92 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 232)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 183 232 (Eq.refl Bool.true) (allA_succ_of_accept 49 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 232
  (Polychromatic418967fa.accept_13_9_1_11_1_275 48 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 183 232 (accept_3_3 47 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 183 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 183 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 232 (accept_3_3 44 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 232 (accept_3_3 41 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 232 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 232 (accept_3_3 38 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 232
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 232 (accept_3_3 35 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 232 (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 183 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 232 (accept_3_3 32 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 232 (accept_3_3 29 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 232 (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 232 (accept_3_3 26 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 232 (accept_3_3 23 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 232 (accept_3_3 20 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 232 (accept_3_3 17 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 232 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 232 (accept_3_3 14 183 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 232
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 232 (accept_3_3 11 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 183 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 232 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 232 (accept_3_3 8 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 232 (accept_3_3 5 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 183 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 232 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 232 (accept_3_3 2 183 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  232)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 182 232 (Eq.refl Bool.true) (allA_of_3_1 51 182
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 181 232 (Eq.refl Bool.true) (allA_succ_of_accept 51 181
  232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 232 (accept_3_3 50 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 232 (accept_3_3 47 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 232 (accept_3_3 44 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 232 (accept_3_3 41 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 232 (accept_3_3 38 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 232 (accept_3_3 35 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 181
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 232 (accept_3_3 32 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 232 (accept_3_3 29 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 232 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 232 (accept_3_3 26 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 232 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 232 (accept_3_3 23 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 232 (accept_3_3 20 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 232 (Polychromatic418967fa.accept_22_18_5_12_1_4337 18 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 232 (accept_3_3 17 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 181 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 232 (accept_3_3 14 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 232 (accept_3_3 11 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 232 (accept_3_3 8 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 232 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 232 (accept_3_3 5 181 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 181 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 232 (accept_3_3 2 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 232 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 181 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 232)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 180 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 180 232 4 13 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 180 232 (Polychromatic418967fa.accept_16_3_4_8_1_3450 51 180 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 180 232 2 25 90 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 232
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 49 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 232 4 12 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 232 (accept_3_3 47 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 180 232 2 23 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 180 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 180 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 180 232 4 11 45 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 232
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 43 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 232 2 21 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 232 (accept_3_3 41 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 232 4 10 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 180 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 232 2 19 90 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 232
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 37 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 232 4 9 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 232 (accept_3_3 35 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  180 232 2 17 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 180 232 (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 180 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 232 4 8 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 232 2 15 90 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 232 (accept_3_3 29
  180 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 232 4 7 45 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 232 2 13 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 180 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 232 4 6 45 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 232 (accept_3_3 23 180 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 232 2 11 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 232 (Polychromatic418967fa.accept_16_5_4_8_1_1560
  21 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 232 4 5 45 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 232
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 232 2 9 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 232 (accept_3_3 17 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 232 4 4 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 180 232 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 180 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 232 2 7 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 232 4 3 45 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 232 (accept_3_3 11
  180 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 232 2 5 90 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 232
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 232 4 2 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 232 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 180 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 232 2 3 90 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 232 (accept_3_3 5 180 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 232 4 1 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 232 2 1 90 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 232
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 180 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 232))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 179 232 (Eq.refl Bool.true)
  (allA_of_3_1 54 179 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 178 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 178 232 2 27 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 232 (accept_3_3 53 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 232 2 26 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 232 2 25 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 232 2 24 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 232 (accept_3_3 47 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 232 2 23 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 232 2 22 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 232
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 232 2 21 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 232 (accept_3_3 41 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 232 2 20 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 232 2 19 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 232 2 18 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 232 (accept_3_3 35 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 232 2 17 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 232 2 16 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 232 2 15 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 232 (accept_3_3 29 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 232 2 14 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 232 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 178 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 232 2 13 89 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 232 2 12 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 232 (accept_3_3 23 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 232 2 11 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 232 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 178 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 232 2 10 89 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 232 2 9 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 232 (accept_3_3 17 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 232 2 8 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 232 2 7 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 232 2 6 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 232 (accept_3_3 11 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 232 2 5 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 178 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 232 2 4 89 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 232 2 3 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 232 (accept_3_3 5 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  232 2 2 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 232 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 178 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 232 2 1 89 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 232 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 178 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 177 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 177
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 232 (accept_3_3 53 177
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 177 232 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 232 (accept_3_3 50 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 232 (Polychromatic418967fa.accept_7_6_2_1_1_214
  48 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 232 (accept_3_3 47
  177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 177 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 232 (accept_3_3 44 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 232 (Polychromatic418967fa.accept_12_6_9_4_1_96
  42 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 232 (accept_3_3 41
  177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 177 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 232 (accept_3_3 38 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 232
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 232 (accept_3_3 35 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 177 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 232 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 177
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 232 (accept_3_3 32 177
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 232 (accept_3_3 29 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 232 (accept_3_3 26 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 232 (accept_3_3 23 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 232 (accept_3_3 20 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 232 (accept_3_3 17 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 232 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 232 (accept_3_3 14 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 232 (accept_3_3 11 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 232 (accept_3_3 8 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 232 (accept_3_3 5 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 177 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 232 (accept_3_3 2 177 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 176 232 (Eq.refl Bool.true) (allA_of_3_1 57
  176 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 175 232 (Eq.refl Bool.true) (allA_succ_of_accept 57
  175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 175 232 (accept_3_3 56 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 175 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 232 (Polychromatic418967fa.accept_21_12_7_1_1_9465 54 175
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 232 (accept_3_3 53 175
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 232
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 232 (accept_3_3 50 175 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 175 232 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 232 (accept_3_3 47 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 232 (accept_3_3 44 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 232 (accept_3_3 41 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 232 (Polychromatic418967fa.accept_17_6_5_11_1_4073 40 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 232 (accept_3_3 38 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 232
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 232 (accept_3_3 35 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 232 (accept_3_3 32 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 232 (accept_3_3 29 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 232 (accept_3_3 26 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 232 (Polychromatic418967fa.accept_16_9_15_8_1_3425 25 175 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 232 (accept_3_3 23 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 232 (accept_3_3 20 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 232
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 232 (accept_3_3 17 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 232 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 232 (accept_3_3 14 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 232 (accept_3_3 11 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 232 (accept_3_3 8 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 232 (accept_3_3 5 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 232 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 175 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 232 (accept_3_3 2 175 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 175 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 174 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 174 232 58 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 174 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 174 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 174 232 2 28 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 55
  174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 232 2 27 87 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 232 (accept_3_3 53
  174 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 232 2 26 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 232 2 25 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 174 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 174 232 2 24 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 174 232 (accept_3_3 47 174 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 232 2 23 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 232 (Polychromatic418967fa.accept_12_9_6_4_1_402
  45 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 232 2 22 87 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 232
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 232 2 21 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 232 (accept_3_3 41 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 232 2 20 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 174 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 232 2 19 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 232 2 18 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 232 (accept_3_3 35 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 232 2 17 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 174 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 232 2 16 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 232 2 15 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 29 174 232 29 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 174 232 2 14 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 174 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 174 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 232 2 13 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 232
  (Polychromatic418967fa.accept_19_6_3_4_1_7040 25 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 232 2 12 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 232 (accept_3_3 23 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 232 2 11 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 232 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 174 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 232 2 10 87 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 232 2 9 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 232 (accept_3_3 17 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 232 2 8 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 174 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 232 2 7 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 232 2 6 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 232 (accept_3_3 11 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 232 2 5 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 174 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 232 2 4 87 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 232 2 3 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 232 (accept_3_3 5 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  232 2 2 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 174 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 232 2 1 87 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 173 232 (Eq.refl Bool.true) (allA_of_3_1
  60 173 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 172 232 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  172 232 4 15 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 172 232 (accept_3_3 59 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  172 232 2 29 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 172 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 172 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 232 4 14 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 232 (Polychromatic418967fa.accept_16_7_12_8_1_2450
  55 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 172 232 2 27 86 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 172 232
  (accept_3_3 53 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 172 232 4 13 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 172 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 172 232 2 25 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 172 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 172 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 172 232 4 12 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 172 232 (accept_3_3 47 172 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 172 232 2 23 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 172 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 45
  172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 232 4 11 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 232
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 43 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 172 232 2 21 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 172 232 (accept_3_3 41 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 232 4 10 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 172 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 232 2 19 86 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 232
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 37 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 232 4 9 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 232 (accept_3_3 35 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 232 2 17 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 172 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 232 4 8 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 31
  172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 232 2 15 86 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 232 (accept_3_3 29
  172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 232 4 7 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 232
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 232 2 13 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 232 (Polychromatic418967fa.accept_14_11_4_8_1_664 25 172 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 232 4 6 43 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 232 (accept_3_3 23 172 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 232 2 11 86 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 232 4 5 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 172 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 232 2 9 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 232 (accept_3_3 17 172 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 232 4 4 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 172 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 232 2 7 86 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 232 4 3 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 172 232 (accept_3_3 11 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  172 232 2 5 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 172 232 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 172 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 232 4 2 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 232 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 172 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 232 2 3 86 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 232 (accept_3_3 5
  172 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 232 4 1 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 172 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 232 2 1 86 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 232 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 172 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172 232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 171 232 (Eq.refl Bool.true) (allA_succ_of_accept 61 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 171 232 (accept_3_3 59 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 171 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 171 232 (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 232 (accept_3_3 56 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 232 (accept_3_3 53 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 171 232 (Polychromatic418967fa.accept_16_4_11_8_1_1574 52 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 232 (accept_3_3 50 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 232
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 232 (accept_3_3 47 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 232 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 232 (accept_3_3 44 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 232 (accept_3_3 41 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 232 (accept_3_3 38 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 232
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 232 (accept_3_3 35 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 232 (Polychromatic418967fa.accept_24_10_3_16_1_2036 34 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 232 (accept_3_3 32 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 232 (accept_3_3 29 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 232 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 232 (accept_3_3 26 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 232
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 24 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 232 (accept_3_3 23 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 232 (Polychromatic418967fa.accept_13_9_2_11_1_1964 22 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 232 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 232 (accept_3_3 20 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 232 (accept_3_3 17 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 232 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 232 (accept_3_3 14 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 232 (accept_3_3 11 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 232 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 232 (accept_3_3 8 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 232
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 232 (accept_3_3 5 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 171 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 232 (accept_3_3 2 171 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 170 232 (Eq.refl Bool.true)
  (allA_of_3_1 63 170 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 169 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 169 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 232 (accept_3_3 62 169 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 169 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 232
  (Polychromatic418967fa.accept_16_12_9_8_1_2508 60 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 232 (accept_3_3 59 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 232 (accept_3_3 56 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 232 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 232
  (Polychromatic418967fa.accept_22_10_15_12_1_4354 54 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 169 232 (accept_3_3 53 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 169 232 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 169 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 232 (accept_3_3 50 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 232 (Polychromatic418967fa.accept_14_7_1_8_1_2873
  49 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 232
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 48 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 232 (accept_3_3 47 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 232 (accept_3_3 44 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 232 (Polychromatic418967fa.accept_20_3_9_12_1_6671 43 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 232
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 42 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 232 (accept_3_3 41 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 232 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 232 (accept_3_3 38 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 169 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 232
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 232 (accept_3_3 35 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 232 (accept_3_3 32 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 169 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 232
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 232 (accept_3_3 29 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 232 (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 232 (accept_3_3 26 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 232 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 232
  (Polychromatic418967fa.accept_23_1_8_2_1_13885 24 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 232 (accept_3_3 23 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 232 (accept_3_3 20 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 232 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 169 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 232
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 232 (accept_3_3 17 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 232 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 232 (accept_3_3 14 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 232 (Polychromatic418967fa.accept_19_13_17_4_1_4228 13 169 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 232
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 12 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 232 (accept_3_3 11 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 232 (accept_3_3 8 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 169 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 232
  (Polychromatic418967fa.accept_19_6_17_4_1_8491 6 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 232 (accept_3_3 5 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 232 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 169 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 232 (accept_3_3 2 169 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 169 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 168 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 168 232 8 8 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 168 232 (Polychromatic418967fa.accept_25_13_18_7_1_13884 63 168 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 168 232 2 31 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 232
  (Polychromatic418967fa.accept_22_17_14_12_1_12335 61 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 168 232 4 15 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 168 232 (accept_3_3 59 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 232 2 29 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 168 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 168 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 232 8 7 21 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 232 2 27 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 232 (accept_3_3 53 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 232 4 13 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 168 232 (Polychromatic418967fa.accept_18_15_6_16_1_4730 51 168 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 232 2 25 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 232 8 6 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 168 232 (accept_3_3 47 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  168 232 2 23 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 168 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 168 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 232 4 11 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 232
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 43 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 168 232 2 21 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 168 232 (accept_3_3 41 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 232 8 5 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 168 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 168 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 232 2 19 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 232 4 9 42 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 232 (accept_3_3 35
  168 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 232 2 17 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 232
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 232 8 4 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 232 2 15 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 232 (accept_3_3 29 168 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 232 4 7 42 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 232
  (Polychromatic418967fa.accept_13_1_12_11_1_728 27 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 232 2 13 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 168 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 232 8 3 21 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 232 (accept_3_3 23 168 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 232 2 11 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 232 4 5 42 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 232 2 9 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 232 (accept_3_3 17 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 232 8 2 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 168 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 168 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 232 2 7 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 232 4 3 42 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 232 (accept_3_3 11
  168 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 232 2 5 84 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 232
  (Polychromatic418967fa.accept_19_9_16_4_1_5584 9 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 232 8 1 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 232 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 168 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 232 2 3 84 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 232 (accept_3_3 5 168 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 232 4 1 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 232 2 1 84 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 167 232 (Eq.refl
  Bool.true) (allA_of_3_1 66 167 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 166 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 166 232 2 33 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 232 (accept_3_3 65 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 232 2 32 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 232 (Polychromatic418967fa.accept_17_12_13_11_1_2910 63 166 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 232 2 31 83 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 232 2 30 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 232 (accept_3_3 59 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 232 2 29 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 232 2 28 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 232 2 27 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 232 (accept_3_3 53 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 232 2 26 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 232 2 25 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 232 2 24 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 232 (accept_3_3 47 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 232 2 23 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 232 2 22 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 232 2 21 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 232 (accept_3_3 41 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 232 2 20 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 232 2 19 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 232 2 18 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 232 (accept_3_3 35 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 232 2 17 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 232 2 16 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 232 2 15 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 232 (accept_3_3 29 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 232 2 14 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 232 2 13 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 232 2 12 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 232 (accept_3_3 23 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 232 2 11 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 232 2 10 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 232 2 9 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 232 (accept_3_3 17 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 232 2 8 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 232 2 7 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 232 2 6 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 232 (accept_3_3 11 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 232 2 5 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 232 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 166 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 232 2 4 83 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 232 2 3 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 232 (accept_3_3 5 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  232 2 2 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 166 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 232 2 1 83 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 166 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 165 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 165 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 232 (accept_3_3 65 165 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 64
  165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 232
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 165 232 (accept_3_3 62 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 165 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 232 (accept_3_3 59 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 232
  (Polychromatic418967fa.accept_10_7_5_2_1_880 57 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 165 232 (accept_3_3 56 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 165 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 232 (accept_3_3 53 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 165 232 (accept_3_3 50 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 165 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 232 (accept_3_3 47 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 165 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 165 232 (accept_3_3 44 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 165 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 232 (accept_3_3 41 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 232
  (Polychromatic418967fa.accept_23_16_4_2_1_13883 39 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 232 (accept_3_3 38 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 232 (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 165
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 232 (accept_3_3 35 165
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 232
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 34 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 165 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 232 (accept_3_3 32 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 232 (Polychromatic418967fa.accept_12_6_9_4_1_96
  30 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 232 (accept_3_3 29
  165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 28 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 165 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 232 (accept_3_3 26 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 232 (accept_3_3 23
  165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 22 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 165 232 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 232 (accept_3_3 20 165 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 232 (Polychromatic418967fa.accept_10_8_5_2_1_881
  18 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 232 (accept_3_3 17
  165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 232
  (Polychromatic418967fa.accept_17_16_12_11_1_6504 16 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 232 (accept_3_3 14 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 232 (accept_3_3 11 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 232 (Polychromatic418967fa.accept_19_9_13_4_1_2982 9 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 232 (accept_3_3 8 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 232 (accept_3_3 5 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 165 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 232 (accept_3_3 2 165 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 164 232 (Eq.refl Bool.true)
  (allA_of_3_1 69 164 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 163 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 163 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 232 (accept_3_3 68 163 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 232 (Polychromatic418967fa.accept_7_3_2_1_1_225
  66 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 232 (accept_3_3 65
  163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 232
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 64 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 232 (accept_3_3 62 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 61 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 232 (accept_3_3 59 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 232 (accept_3_3 56 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 232
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 232 (accept_3_3 53 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 232 (accept_3_3 50 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 232 (accept_3_3 47 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 232 (accept_3_3 44 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 232 (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 163 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 232 (accept_3_3 41 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 232 (accept_3_3 38 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 232 (Polychromatic418967fa.accept_16_5_3_8_1_4555 37 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 232
  (Polychromatic418967fa.accept_15_6_13_7_1_222 36 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 232 (accept_3_3 35 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 232 (accept_3_3 32 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 232 (accept_3_3 29 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 232 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 232 (accept_3_3 26 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 232 (accept_3_3 23 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 232 (accept_3_3 20 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 232 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 163 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 232
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 232 (accept_3_3 17 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 232 (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 232 (accept_3_3 14 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 232 (accept_3_3 11 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 232 (accept_3_3 8 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 232 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 232 (accept_3_3 5 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 232 (accept_3_3 2 163 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 163 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 162 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 162 232 2 35 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 162 232 2 34 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 232
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 67 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 232 2 33 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 232 (accept_3_3 65 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 232 2 32 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 232 2 31 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 232
  (Polychromatic418967fa.accept_21_19_15_1_1_6345 61 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 162 232 2 30 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 162 232 (accept_3_3 59 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 232 2 29 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 232 2 28 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 232
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 162 232 2 27 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 162 232 (accept_3_3 53 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 232 2 26 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 232 2 25 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 232
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 49 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 232 2 24 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 232 (accept_3_3 47 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 232 2 23 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 232 2 22 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 232
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 43 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 232 2 21 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 232 (accept_3_3 41 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 232 2 20 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 232 2 19 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 232
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 232 2 18 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 232 (accept_3_3 35 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 232 2 17 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 232 2 16 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 232
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 232 2 15 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 232 (accept_3_3 29 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 232 2 14 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 232 2 13 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 232
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 162 232 2 12 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 232 (accept_3_3 23 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 232 2 11 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 232 2 10 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 232
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 232 2 9 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 232 (accept_3_3 17 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 232 2 8 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 162 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 232 2 7 81 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 232
  (Polychromatic418967fa.accept_19_13_10_4_1_4258 13 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 232 2 6 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 232 (accept_3_3 11 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 232 2 5 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 232 2 4 81 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 232
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 7 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 232 2 3 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 232 (accept_3_3 5 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  232 2 2 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 162 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 232 2 1 81 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 232 (Polychromatic418967fa.accept_19_1_10_4_1_2965 1 162 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 161 232 (Eq.refl Bool.true)
  (allA_of_3_1 72 161 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 160 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 160 232 8 9 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 160 232 (accept_3_3 71 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  160 232 2 35 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 160 232 (Polychromatic418967fa.accept_17_1_7_11_1_2892 69 160 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 232 4 17 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 232 (Polychromatic418967fa.accept_13_2_4_11_1_2003
  67 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 232 2 33 80 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 232
  (accept_3_3 65 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 232 8 8 20 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 232
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 160 232 2 31 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 160 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 160 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 232 4 15 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 232 (accept_3_3 59 160 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 232 2 29 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 232
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 57 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 160 232 8 7 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 160 232 (Polychromatic418967fa.accept_19_17_8_4_1_4212 55 160 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 160 232 2 27 80 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 232 (accept_3_3 53 160 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 232 4 13 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 160 232 2 25 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 160 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 160 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 160 232 8 6 20 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 160 232 (accept_3_3 47 160 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 160 232 2 23 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 160 232 (Polychromatic418967fa.accept_13_6_4_11_1_282
  45 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 232 4 11 40 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 232
  (Polychromatic418967fa.accept_19_5_8_4_1_4289 43 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 160 232 2 21 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 160 232 (accept_3_3 41 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 232 8 5 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 160 232 (Polychromatic418967fa.accept_17_5_7_11_1_5274 39 160 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 232 2 19 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 37
  160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 232 4 9 40 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 232 (accept_3_3 35
  160 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 232 2 17 80 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 232 8 4 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 232 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 160 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 232 2 15 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 232 (accept_3_3 29 160 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 232 4 7 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 160 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 232 2 13 80 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 232
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 160 232 8 3 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 160 232 (accept_3_3 23 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 232 2 11 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 232 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 160 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 232 4 5 40 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 232 2 9 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 232 (accept_3_3 17 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 232 8 2 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 160 232 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 160 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 232 2 7 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 232
  (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 160 232 4 3 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 160 232 (accept_3_3 11 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 232 2 5 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 160 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 232 8 1 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 232 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7
  160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 232 2 3 80 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 232 (accept_3_3 5
  160 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 232 4 1 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 232
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 3 160 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 232 2 1 80 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 232 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 160 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 159 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 232 (Polychromatic418967fa.accept_11_6_5_1_1_586
  72 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 232 (accept_3_3 71
  159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 232
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 70 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 159 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 159 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 232 (accept_3_3 68 159 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 66
  159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 232 (accept_3_3 65
  159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 159 232 (Polychromatic418967fa.accept_17_12_6_11_1_7880 63 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 232 (accept_3_3 62 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 232 (accept_3_3 59 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 232 (accept_3_3 56 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 232 (accept_3_3 53 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 232 (accept_3_3 50 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 232 (accept_3_3 47 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 232 (accept_3_3 44 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 232 (accept_3_3 41 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 232 (accept_3_3 38 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 232
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 232 (accept_3_3 35 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 159 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 232 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 159
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 232 (accept_3_3 32 159
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 232 (accept_3_3 29 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 232 (accept_3_3 26 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 232 (accept_3_3 23 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 232 (accept_3_3 20 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 232 (accept_3_3 17 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 232 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 232 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 232 (accept_3_3 14 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 232 (accept_3_3 11 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 232 (Polychromatic418967fa.accept_16_9_15_8_1_3425 9 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 232 (accept_3_3 8 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 232 (accept_3_3 5 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 159 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 232 (accept_3_3 2 159 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 158 232 (Eq.refl
  Bool.true) (allA_of_3_1 75 158 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 157 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 232 (accept_3_3 74 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 157 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 232 (accept_3_3 71
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 232
  (Polychromatic418967fa.accept_12_10_1_4_1_392 70 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 232 (accept_3_3 68 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 66
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 232 (accept_3_3 65
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 64 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 232 (accept_3_3 62 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 157 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 232 (accept_3_3 59
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 58 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 232 (accept_3_3 56 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 157 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 232 (Polychromatic418967fa.accept_7_5_3_1_1_424
  54 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 232 (accept_3_3 53
  157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 232
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 52 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 232 (accept_3_3 50 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 157 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 232 (accept_3_3 47 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 232 (accept_3_3 44 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 232 (Polychromatic418967fa.accept_16_11_13_8_1_1578 43 157 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 232 (accept_3_3 41 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 232 (accept_3_3 38 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 232
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 157 232 (accept_3_3 35 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 157 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 157 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 232 (accept_3_3 32 157 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 232
  (Polychromatic418967fa.accept_19_12_5_4_1_11267 31 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 232 (accept_3_3 29 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 232 (accept_3_3 26 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 232 (accept_3_3 23 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 232 (accept_3_3 20 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 232 (accept_3_3 17 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 232 (accept_3_3 14 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 232 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 232 (accept_3_3 11 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 232 (accept_3_3 8 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 232 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 232 (accept_3_3 5 157 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 232 (accept_3_3 2 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 156 232 (Eq.refl Bool.true) (allA_succ_of_gcd 76 156 232 4 19 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 232
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 75 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 156 232 2 37 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 156 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 232 4 18 39 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 232 (accept_3_3 71 156 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 232 2 35 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 232 4 17 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 156 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 232 2 33 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 232 (accept_3_3 65 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 232 4 16 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 232
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 63 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 156 232 2 31 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 61 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 232 4 15 39 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 232 (accept_3_3 59 156 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 232 2 29 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 232
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 232 4 14 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 156 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 232 2 27 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 232 (accept_3_3 53 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 232 4 13 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 51
  156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 232 2 25 78 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 232 4 12 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 232 (accept_3_3 47 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 232 2 23 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 156 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 232 4 11 39 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 232
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 232 2 21 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 232 (accept_3_3 41 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 232 4 10 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 232 (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 232 2 19 78 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 232 4 9 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 232 (accept_3_3 35 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 232 2 17 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 156 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 232 4 8 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 31
  156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 232 2 15 78 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 232 (accept_3_3 29
  156 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 232 4 7 39 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 232 2 13 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 232 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 156 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 232 4 6 39 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 232 (accept_3_3 23 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 232 2 11 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 232 (Polychromatic418967fa.accept_10_1_6_2_1_867
  21 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 232 4 5 39 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 232 2 9 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 232 (accept_3_3 17 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 232 4 4 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 156 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 156 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 232 2 7 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 232 4 3 39 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 232 (accept_3_3 11
  156 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 232 2 5 78 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 232
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 232 4 2 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 232 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 156 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 232 2 3 78 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 232 (accept_3_3 5 156 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 232 4 1 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 232 2 1 78 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 156 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 155 232
  (Eq.refl Bool.true) (allA_of_3_1 78 155 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 154 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 154 232 2 39 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 154 232 (accept_3_3 77 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 232 2 38 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 232 2 37 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 232 2 36 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 232 (accept_3_3 71 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 232 2 35 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 232 2 34 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 232 2 33 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 232 (accept_3_3 65 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 232 2 32 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 232 (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 154 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 232 2 31 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 232 2 30 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 232 (accept_3_3 59 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 232 2 29 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 232 2 28 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 232 2 27 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 232 (accept_3_3 53 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 232 2 26 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 232 2 25 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 232 2 24 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 232 (accept_3_3 47 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 232 2 23 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 232 (Polychromatic418967fa.accept_19_7_2_4_1_12590 45 154 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 232 2 22 77 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 232 2 21 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 232 (accept_3_3 41 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 232 2 20 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 232 2 19 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 232 2 18 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 232 (accept_3_3 35 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 232 2 17 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 232 2 16 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 232 2 15 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 232 (accept_3_3 29 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 232 2 14 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 232 2 13 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 232 2 12 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 232 (accept_3_3 23 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 232 2 11 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 232 2 10 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 232 2 9 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 232 (accept_3_3 17 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 232 2 8 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 232 2 7 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 232 2 6 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 232 (accept_3_3 11 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 232 2 5 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 232 (Polychromatic418967fa.accept_19_9_2_4_1_7038 9 154 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 232 2 4 77 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 232 2 3 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 232 (accept_3_3 5 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  232 2 2 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 232 2 1 77 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 232 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 153 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 232 (Polychromatic418967fa.accept_12_6_9_4_1_96
  78 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 232 (accept_3_3 77
  153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 232
  (Polychromatic418967fa.accept_16_12_9_8_1_2508 76 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 153 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 153 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 232 (accept_3_3 74 153 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 72
  153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 232 (accept_3_3 71
  153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 232
  (Polychromatic418967fa.accept_15_10_3_7_1_715 70 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 153 232 (Polychromatic418967fa.accept_13_4_10_11_1_1908 69 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 232 (accept_3_3 68 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 153 232 (accept_3_3 65 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 153 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 64 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 232 (Polychromatic418967fa.accept_14_7_13_8_1_2067 63 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 232 (accept_3_3 62 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 232
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 60 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 232 (accept_3_3 59 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 153 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 153 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 232 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 153
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 232 (accept_3_3 56 153
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  55 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 232 (accept_3_3 53 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 232 (Polychromatic418967fa.accept_16_4_9_8_1_2509 52 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 232 (accept_3_3 50 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 232
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 232 (accept_3_3 47 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 232 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 153 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 153
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 232 (accept_3_3 44 153
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 232
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 232 (accept_3_3 41 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 232 (Polychromatic418967fa.accept_16_7_9_8_1_829 39 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 232 (accept_3_3 38 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 232
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 232 (accept_3_3 35 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 232 (Polychromatic418967fa.accept_13_8_10_11_1_2730 34 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 232 (accept_3_3 32 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 232 (accept_3_3 29 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 232 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 232 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 232 (accept_3_3 26 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 232
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 232 (accept_3_3 23 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 232 (Polychromatic418967fa.accept_19_3_1_4_1_1860 22 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 232 (accept_3_3 20 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 232 (accept_3_3 17 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 232 (accept_3_3 14 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 232 (accept_3_3 11 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 232 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 232 (accept_3_3 8 153 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 232 (accept_3_3 5 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 232 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 153 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 232 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 232 (accept_3_3 2 153 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 152 232 (Eq.refl
  Bool.true) (allA_of_3_1 81 152 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 151 232 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 151 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 151 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 232 (accept_3_3 80 151 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 151 232 (Polychromatic418967fa.accept_10_9_1_2_1_522 79 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 232
  (Polychromatic418967fa.accept_19_2_18_4_1_8509 78 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 232 (accept_3_3 77 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 232 (accept_3_3 74 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 232
  (Polychromatic418967fa.accept_17_4_15_11_1_6465 72 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 151 232 (accept_3_3 71 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 151 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 151 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 151 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 232 (accept_3_3 68 151 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 232
  (Polychromatic418967fa.accept_17_16_15_11_1_10421 67 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 232 (accept_3_3 65 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 232 (Polychromatic418967fa.accept_17_13_15_11_1_2936 64 151 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 232 (accept_3_3 62 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 232 (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 232 (accept_3_3 59 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 151
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 232 (accept_3_3 56 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 232 (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 232 (accept_3_3 53 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 232 (accept_3_3 50 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 232 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 232 (accept_3_3 47 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 151
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 232 (accept_3_3 44 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 232 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 232 (accept_3_3 41 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 151 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 232 (accept_3_3 38 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 232 (accept_3_3 35 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 151
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 232 (accept_3_3 32 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 232 (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 232 (accept_3_3 29 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 232 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 151
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 232 (accept_3_3 26 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 232 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 232 (accept_3_3 23 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 232 (accept_3_3 20 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 232 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 232 (accept_3_3 17 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 151
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 232 (accept_3_3 14 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 232 (accept_3_3 11 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 232 (accept_3_3 8 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 232 (Polychromatic418967fa.accept_21_7_4_1_1_3300 7 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 232 (accept_3_3 5 151 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 151 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 232 (accept_3_3 2 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 232 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 151 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 150 232 (Eq.refl Bool.true) (allA_succ_of_gcd 82 150 232 2 41 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 232 2 40 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 232 2 39 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 232 (accept_3_3 77 150 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 232 2 38 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 75
  150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 150 232 2 37 75 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 232 2 36 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 232 (accept_3_3 71 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 232 2 35 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 232 2 34 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 232 2 33 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 232 (accept_3_3 65 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 232 2 32 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 232 2 31 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 232 2 30 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 232 (accept_3_3 59 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 232 2 29 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 232 2 28 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 232 2 27 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 232 (accept_3_3 53 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 232 2 26 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 232 2 25 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 232 2 24 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 232 (accept_3_3 47 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 232 2 23 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 232 2 22 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 232
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 232 2 21 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 232 (accept_3_3 41 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 232 2 20 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 232 2 19 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 232 2 18 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 232 (accept_3_3 35 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 232 2 17 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 232 2 16 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 232 2 15 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 232 (accept_3_3 29 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 232 2 14 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 232 2 13 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 232 2 12 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 232 (accept_3_3 23 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 232 2 11 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 232 2 10 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 232 2 9 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 232 (accept_3_3 17 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 232 2 8 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 232 2 7 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 232 2 6 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 232 (accept_3_3 11 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 232 2 5 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 232 2 4 75 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 232
  (Polychromatic418967fa.accept_21_7_3_1_1_3321 7 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 232 2 3 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 232 (accept_3_3 5 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  232 2 2 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 232 2 1 75 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 150 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 150 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 149 232 (Eq.refl
  Bool.true) (allA_of_3_1 84 149 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 148 232 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 148 232 4 21 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 232 (accept_3_3 83 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 232 2 41 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 232 (Polychromatic418967fa.accept_13_3_5_11_1_716 81 148 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 232 4 20 37 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 232
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 79 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 232 2 39 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 232 (accept_3_3 77 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 232 4 19 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 232 2 37 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 232 4 18 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 232 (accept_3_3 71 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 232 2 35 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 232 4 17 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 232
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 67 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 232 2 33 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 232 (accept_3_3 65 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 232 4 16 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 232 (Polychromatic418967fa.accept_16_15_4_8_1_1562 63 148 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 232 2 31 74 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 232
  (Polychromatic418967fa.accept_11_6_5_1_1_586 61 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 232 4 15 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 232 (accept_3_3 59 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 232 2 29 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 232 4 14 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 232 2 27 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 232 (accept_3_3 53 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 232 4 13 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 232 2 25 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 232
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 49 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 232 4 12 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 232 (accept_3_3 47 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 232 2 23 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 232 4 11 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 232
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 43 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 232 2 21 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 232 (accept_3_3 41 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 232 4 10 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 232 2 19 74 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 232 4 9 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 232 (accept_3_3 35 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 232 2 17 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 148 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 232 4 8 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 232 (Polychromatic418967fa.accept_16_15_4_8_1_1562
  31 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 232 2 15 74 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 232
  (accept_3_3 29 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 232 4 7 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 232
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 148 232 2 13 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 148 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 232 4 6 37 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 232 (accept_3_3 23 148 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 232 2 11 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 232 4 5 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 232 2 9 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 232 (accept_3_3 17 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 232 4 4 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 148 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 232 2 7 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 232 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 232 4 3 37 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 232
  (accept_3_3 11 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 232 2 5 74 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 232
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 232 4 2 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 232 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 148 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 232 2 3 74 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 232 (accept_3_3 5 148 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 232 4 1 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 148 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 232 2 1 74 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  147 232 (Eq.refl Bool.true) (allA_succ_of_accept 85 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 232
  (Polychromatic418967fa.accept_10_4_7_2_1_211 84 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 147 232 (accept_3_3 83 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 147 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 147 232 (Polychromatic418967fa.accept_15_6_12_7_1_1360 81 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 232 (accept_3_3 80 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 147 232 (accept_3_3 77 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 147 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 147 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 232 (accept_3_3 74 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 232
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 72 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 147 232 (accept_3_3 71 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 147 232 (Polychromatic418967fa.accept_15_10_12_7_1_1358 70 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 147 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 232 (accept_3_3 68 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 232 (accept_3_3 65 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 232 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 232 (accept_3_3 62 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 232 (accept_3_3 59 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 147 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 147 232 (Polychromatic418967fa.accept_14_1_7_8_1_2063 57 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 232 (accept_3_3 56 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 232
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 232 (accept_3_3 53 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 232 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 232 (accept_3_3 50 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 232
  (Polychromatic418967fa.accept_14_6_7_8_1_624 48 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 147 232 (accept_3_3 47 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 147 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 147 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 232 (accept_3_3 44 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 147 232 (accept_3_3 41 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 147 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 147 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 232 (accept_3_3 38 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 232
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 232 (accept_3_3 35 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 147 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 232 (accept_3_3 32 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 232
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 232 (accept_3_3 29 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 232 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 232 (accept_3_3 26 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 232 (accept_3_3 23 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 232 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 232 (accept_3_3 20 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 232 (accept_3_3 17 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 232 (Polychromatic418967fa.accept_23_16_9_2_1_9078 16 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 232 (accept_3_3 14 147 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 232
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 232 (accept_3_3 11 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 147 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 232 (accept_3_3 8 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 232 (accept_3_3 5 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 232 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 232 (accept_3_3 2 147 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 146 232
  (Eq.refl Bool.true) (allA_of_3_1 87 146 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 145 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 145 232 29 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 145 232 (accept_3_3 86 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 145 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 145 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 232 (accept_3_3 83 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 232 (Polychromatic418967fa.accept_12_10_1_4_1_392
  82 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 232 (accept_3_3 80 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 232 (Polychromatic418967fa.accept_15_4_10_7_1_1356 79 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 232 (accept_3_3 77 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 232 (accept_3_3 74 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 232 (Polychromatic418967fa.accept_15_12_10_7_1_1357 72 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 232 (accept_3_3 71 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 145
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 232 (accept_3_3 68 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 232 (accept_3_3 65 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 232 (Polychromatic418967fa.accept_15_4_10_7_1_1356 64 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 232 (accept_3_3 62 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 232 (Polychromatic418967fa.accept_13_9_2_11_1_1964 61 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 232 (accept_3_3 59 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 145 232 29 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 232 (accept_3_3 56 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 232
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 232 (accept_3_3 53 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 232 (accept_3_3 50 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 232 (accept_3_3 47 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 232 (accept_3_3 44 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 232
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 232 (accept_3_3 41 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 232 (accept_3_3 38 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 232
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 232 (accept_3_3 35 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 232 (accept_3_3 32 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 29 145 232 29 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 28 145 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 145 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 232 (accept_3_3 26 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 232 (Polychromatic418967fa.accept_7_4_5_1_1_418
  25 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 232 (accept_3_3 23 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 232 (accept_3_3 20 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 232 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 145 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 232 (accept_3_3 17 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 232 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 232 (accept_3_3 14 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 232 (accept_3_3 11 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 232 (accept_3_3 8 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 232 (accept_3_3 5 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 232 (accept_3_3 2 145 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 232 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 145 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 144 232
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 144 232 8 11 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 144 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 144 232 2 43 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 232
  (Polychromatic418967fa.accept_13_7_1_11_1_732 85 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 232 4 21 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 232 (accept_3_3 83 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 232 2 41 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 144 232 (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 144 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 144 232 8 10 18 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 232
  (Polychromatic418967fa.accept_19_3_11_4_1_8466 79 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 232 2 39 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 232 (accept_3_3 77 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 232 4 19 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 144 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 144 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 232 2 37 72 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 232 8 9 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 232 (accept_3_3 71 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  144 232 2 35 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 144 232 (Polychromatic418967fa.accept_17_1_8_11_1_6471 69 144 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 232 4 17 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 232 (Polychromatic418967fa.accept_10_7_4_2_1_903
  67 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 232 2 33 72 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 232
  (accept_3_3 65 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 232 8 8 18 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 232
  (Polychromatic418967fa.accept_23_17_6_2_1_2369 63 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 232 2 31 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 144 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 232 4 15 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 232 (accept_3_3 59 144 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 232 2 29 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 232 (Polychromatic418967fa.accept_10_7_4_2_1_903
  57 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 232 8 7 18 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 232
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 55 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 232 2 27 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 232 (accept_3_3 53 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 232 4 13 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 232 (Polychromatic418967fa.accept_13_12_1_11_1_1917 51 144 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 232 2 25 72 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 232
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 49 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 144 232 8 6 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 144 232 (accept_3_3 47 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 232 2 23 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 232 4 11 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 232
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 232 2 21 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 232 (accept_3_3 41 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 232 8 5 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 144 232 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 144 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 232 2 19 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 232 (Polychromatic418967fa.accept_10_7_4_2_1_903
  37 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 232 4 9 36 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 232
  (accept_3_3 35 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 232 2 17 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 232 8 4 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 144 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 232 2 15 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 232 (accept_3_3 29 144 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 232 4 7 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 144 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 232 2 13 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 232
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 144 232 8 3 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 144 232 (accept_3_3 23 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 232 2 11 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 232 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 144 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 232 4 5 36 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 232 2 9 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 232 (accept_3_3 17 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 232 8 2 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 232 (Polychromatic418967fa.accept_19_15_11_4_1_13882 15 144 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 232 2 7 72 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 232
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 232 4 3 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 232 (accept_3_3 11 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  144 232 2 5 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 232 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 144 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 232 8 1 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 232 2 3 72 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 232 (accept_3_3 5
  144 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 232 4 1 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 232 2 1 72 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 232 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 144 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 143 232
  (Eq.refl Bool.true) (allA_of_3_1 90 143 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 142 232 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 142 232 2 45 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 142 232 (accept_3_3 89 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 232 2 44 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 232 2 43 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 232 2 42 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 232 (accept_3_3 83 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 232 2 41 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 232 (Polychromatic418967fa.accept_17_13_6_11_1_4014 81 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 232 2 40 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 232
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 79 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 232 2 39 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 232 (accept_3_3 77 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 232 2 38 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 232 2 37 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 232 2 36 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 232 (accept_3_3 71 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 232 2 35 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 232 2 34 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 232 2 33 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 232 (accept_3_3 65 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 232 2 32 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 232 (Polychromatic418967fa.accept_17_12_6_11_1_7880 63 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 232 2 31 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 232 2 30 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 232 (accept_3_3 59 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 232 2 29 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 232 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 232 2 28 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 232 2 27 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 232 (accept_3_3 53 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 232 2 26 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 232 (Polychromatic418967fa.accept_19_13_9_4_1_4309 51 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 232 2 25 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 232 2 24 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 232 (accept_3_3 47 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 232 2 23 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 232 2 22 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 232 2 21 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 232 (accept_3_3 41 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 232 2 20 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 232 (Polychromatic418967fa.accept_17_5_6_11_1_3974 39 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 232 2 19 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 232 2 18 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 232 (accept_3_3 35 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 232 2 17 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 232 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 232 2 16 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 232 2 15 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 232 (accept_3_3 29 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 232 2 14 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 232 2 13 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 232 2 12 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 232 (accept_3_3 23 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 232 2 11 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 232 (Polychromatic418967fa.accept_17_4_6_11_1_1030 21 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 232 2 10 71 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 232 2 9 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 232 (accept_3_3 17 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 232 2 8 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 232 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 232 2 7 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 232 2 6 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 232 (accept_3_3 11 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 232 2 5 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 232 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 142 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 232 2 4 71 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 232 2 3 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 232 (accept_3_3 5 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  232 2 2 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 232 2 1 71 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 232 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 142 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 141 232
  (Eq.refl Bool.true) (allA_succ_of_accept 91 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 232 (accept_3_3 89 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 232 (Polychromatic418967fa.accept_15_13_6_7_1_1369 88 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 232 (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 232 (accept_3_3 86 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 232 (accept_3_3 83 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 232 (Polychromatic418967fa.accept_18_9_15_16_1_8759 81 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 232 (accept_3_3 80 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 232 (accept_3_3 77 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 232 (accept_3_3 74 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 232
  (Polychromatic418967fa.accept_14_2_1_8_1_650 72 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 232 (accept_3_3 71 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 232 (Polychromatic418967fa.accept_19_13_8_4_1_7047 70 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 232 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 232 (accept_3_3 68 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 232 (accept_3_3 65 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 232 (accept_3_3 62 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 232
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 60 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 232 (accept_3_3 59 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 141 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 232 (accept_3_3 56 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 232
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 232 (accept_3_3 53 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 232 (Polychromatic418967fa.accept_16_4_13_8_1_3424 52 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 232 (Polychromatic418967fa.accept_14_9_1_8_1_2849 51 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 232 (accept_3_3 50 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 232 (accept_3_3 47 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 232 (Polychromatic418967fa.accept_18_9_15_16_1_8759 45 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 232 (accept_3_3 44 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 232 (accept_3_3 41 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 232 (accept_3_3 38 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 232
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 232 (accept_3_3 35 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 232 (Polychromatic418967fa.accept_19_15_8_4_1_2962 34 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 232 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 232 (accept_3_3 32 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 232 (accept_3_3 29 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 232 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 232 (accept_3_3 26 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 232
  (Polychromatic418967fa.accept_17_7_5_11_1_2922 24 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 232 (accept_3_3 23 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 232 (accept_3_3 20 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 232 (accept_3_3 17 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 232 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 232 (Polychromatic418967fa.accept_17_15_5_11_1_6468 15 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 232 (accept_3_3 14 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 232 (accept_3_3 11 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 232 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 232 (accept_3_3 8 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 232
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 232 (accept_3_3 5 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 141 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 232 (accept_3_3 2 141 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 140 232
  (Eq.refl Bool.true) (allA_of_3_1 93 140 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 139 232 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 139 232 (accept_3_3 92 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 139 232
  (Polychromatic418967fa.accept_24_18_19_16_1_5217 90 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 139 232 (accept_3_3 89 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 139 232 (Polychromatic418967fa.accept_19_12_6_4_1_2992 88 139 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 139 232 (accept_3_3 86 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 139 232 (Polychromatic418967fa.accept_13_7_9_11_1_705
  85 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 139 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 139 232 (accept_3_3 83 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 139 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 232 (accept_3_3 80 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 139 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 232 (accept_3_3 77 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 232 (Polychromatic418967fa.accept_16_12_11_8_1_832 76 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 232 (accept_3_3 74 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 232 (accept_3_3 71 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 232 (accept_3_3 68 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 67 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 232 (accept_3_3 65 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 232 (accept_3_3 62 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 232 (accept_3_3 59 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 232 (accept_3_3 56 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 232 (accept_3_3 53 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 232 (Polychromatic418967fa.accept_16_4_11_8_1_1574 52 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 232 (accept_3_3 50 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 232 (Polychromatic418967fa.accept_14_7_13_8_1_2067 49 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 232
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 232 (accept_3_3 47 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 232 (accept_3_3 44 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 232 (Polychromatic418967fa.accept_17_9_3_11_1_3983 43 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 232 (accept_3_3 41 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 232 (accept_3_3 38 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 232
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 232 (accept_3_3 35 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 232 (accept_3_3 32 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 232 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 232 (accept_3_3 29 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 232 (accept_3_3 26 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 232 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 232 (accept_3_3 23 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 232 (accept_3_3 20 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 232
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 232 (accept_3_3 17 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 232 (accept_3_3 14 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 232 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 139 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 232 (accept_3_3 11 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 232 (accept_3_3 8 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 232
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 232 (accept_3_3 5 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 232 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 139 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 232 (accept_3_3 2 139 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 138
  232 (Eq.refl Bool.true) (allA_succ_of_gcd 94 138 232 2 47 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 93 138 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 138 232 2 46 69 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 232 2 45 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 232 (accept_3_3 89 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 138 232 2 44 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 138 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 232 2 43 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 232 2 42 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 232 (accept_3_3 83 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 232 2 41 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 232 2 40 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 232
  (Polychromatic418967fa.accept_13_1_8_11_1_724 79 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 232 2 39 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 232 (accept_3_3 77 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 232 2 38 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 232 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 232 2 37 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 232 2 36 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 232 (accept_3_3 71 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 232 2 35 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 232 2 34 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 232 2 33 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 232 (accept_3_3 65 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 232 2 32 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 232 2 31 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 232
  (Polychromatic418967fa.accept_13_9_8_11_1_725 61 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 232 2 30 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 232 (accept_3_3 59 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 232 2 29 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 232 2 28 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 232 2 27 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 232 (accept_3_3 53 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 232 2 26 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 232 2 25 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 232
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 232 2 24 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 232 (accept_3_3 47 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 232 2 23 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 232 2 22 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 232
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 43 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 232 2 21 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 232 (accept_3_3 41 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 232 2 20 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 232 2 19 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 232 2 18 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 232 (accept_3_3 35 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 232 2 17 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 232 2 16 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 232 2 15 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 232 (accept_3_3 29 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 232 2 14 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 232 2 13 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 232 2 12 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 232 (accept_3_3 23 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 232 2 11 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 232 2 10 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 232
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 232 2 9 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 232 (accept_3_3 17 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 232 2 8 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 232 2 7 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 232 2 6 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 232 (accept_3_3 11 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 232 2 5 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 138 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 232 2 4 69 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 232
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 232 2 3 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 232 (accept_3_3 5 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  232 2 2 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 232 2 1 69 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 138 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 137
  232 (Eq.refl Bool.true) (allA_of_3_1 96 137 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 136 232
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 136 232 8 12 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 136 232 (accept_3_3 95 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 136 232 2 47 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 136 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 136 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 232 4 23 34 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 91 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 136 232 2 45 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 136 232 (accept_3_3 89 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 232 8 11 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 232 2 43 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 232 4 21 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 232 (accept_3_3 83 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 232 2 41 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 232 8 10 17 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 232 2 39 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 232 (accept_3_3 77 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 232 4 19 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 232 2 37 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 232
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 73 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 232 8 9 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 136 232 (accept_3_3 71 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  136 232 2 35 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 136 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 232 4 17 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 136 232 2 33 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 136 232 (accept_3_3 65
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 136 232 8 8 17 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 136 232
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 136 232 2 31 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 136 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 136 232 4 15 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 136 232 (accept_3_3 59 136 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 136 232 2 29 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 136 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 57
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 232 8 7 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 232
  (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 232 2 27 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 232 (accept_3_3 53 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 232 4 13 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 232 2 25 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 232 8 6 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 136 232 (accept_3_3 47 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  136 232 2 23 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 136 232 (Polychromatic418967fa.accept_19_7_3_4_1_13881 45 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 232 4 11 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 232 (Polychromatic418967fa.accept_13_4_6_11_1_2017
  43 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 136 232 2 21 68 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 136 232
  (accept_3_3 41 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 136 232 8 5 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 136 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 136 232 2 19 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 136 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 232 4 9 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 232 (accept_3_3 35 136 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 232 2 17 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 232 8 4 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 232 2 15 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 232 (accept_3_3 29 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 232 4 7 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 136 232 (Polychromatic418967fa.accept_19_8_3_4_1_9865 27 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 232 2 13 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 25
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 232 8 3 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 232 (accept_3_3 23
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 232 2 11 68 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 232 4 5 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 232 2 9 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 232 (accept_3_3 17 136 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 232 8 2 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 136 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 232 2 7 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 232
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 232 4 3 34 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 136 232 (accept_3_3 11 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  136 232 2 5 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 136 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 232 8 1 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 232 (Polychromatic418967fa.accept_19_7_3_4_1_13881 7 136 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 232 2 3 68 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 232 (accept_3_3 5
  136 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 232 4 1 34 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 136 232
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 136 232 2 1 68 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 136 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 136 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 136
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  135 232 (Eq.refl Bool.true) (allA_succ_of_accept 97 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 232
  (Polychromatic418967fa.accept_21_12_9_1_1_9528 96 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 135 232 (accept_3_3 95 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 135 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 93 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 232 (accept_3_3 92 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 135 232 (accept_3_3 89 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 135 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 88 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 232 (accept_3_3 86 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 232
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 84 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 232 (accept_3_3 83 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 232 (Polychromatic418967fa.accept_17_14_16_11_1_3997 82 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 232 (Polychromatic418967fa.accept_13_3_5_11_1_716 81 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 232 (accept_3_3 80 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 232
  (Polychromatic418967fa.accept_10_8_5_2_1_881 78 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 232 (accept_3_3 77 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 135 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 232 (Polychromatic418967fa.accept_19_18_2_4_1_7039 75 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 232 (accept_3_3 74 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 232
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 72 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 232 (accept_3_3 71 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 135 232 (Polychromatic418967fa.accept_20_10_15_12_1_11131 70 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 232 (accept_3_3 68 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 232 (accept_3_3 65 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 232 (Polychromatic418967fa.accept_19_7_2_4_1_12590 64 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 232 (accept_3_3 62 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 232
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 60 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 232 (accept_3_3 59 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 232 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 232 (accept_3_3 56 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 232 (accept_3_3 53 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 232 (Polychromatic418967fa.accept_18_15_9_16_1_6029 51 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 232 (accept_3_3 50 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 135 232 (accept_3_3 47 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 135 232 (Polychromatic418967fa.accept_11_2_3_1_1_244 46 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 232 (accept_3_3 44 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 232 (accept_3_3 41 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 232 (Polychromatic418967fa.accept_23_17_20_2_1_12264 40 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 232 (Polychromatic418967fa.accept_17_5_16_11_1_3998 39 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 232 (accept_3_3 38 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 232
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 232 (accept_3_3 35 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 232 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 232 (accept_3_3 32 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 232
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 232 (accept_3_3 29 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 232 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 232 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 232 (accept_3_3 26 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 232
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 232 (accept_3_3 23 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 232 (Polychromatic418967fa.accept_17_5_16_11_1_3998 22 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 232 (Polychromatic418967fa.accept_22_21_3_12_1_13880 21 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 232 (accept_3_3 20 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 232
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 232 (accept_3_3 17 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 232 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 232 (Polychromatic418967fa.accept_14_1_9_8_1_2863 15 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 232 (accept_3_3 14 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 232
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 232 (accept_3_3 11 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 232 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 232 (accept_3_3 8 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 232
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 232 (accept_3_3 5 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 232 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 135 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 232 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 232 (accept_3_3 2 135 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  134 232 (Eq.refl Bool.true) (allA_of_3_1 99 134 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 133 232
  (Eq.refl Bool.true) (allA_succ_of_accept 99 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 133 232 (accept_3_3 98 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 133 232 (Polychromatic418967fa.accept_14_13_7_8_1_677 97 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 133 232
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 96 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 133 232 (accept_3_3 95 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 133 232 (accept_3_3 92 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 133 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 91 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 133 232
  (Polychromatic418967fa.accept_14_6_7_8_1_624 90 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 133 232 (accept_3_3 89 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 133 232 (Polychromatic418967fa.accept_13_10_3_11_1_1923 88 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 232 (accept_3_3 86 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 133 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 85 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 232
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 84 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 232 (accept_3_3 83 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 232 (accept_3_3 80 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 232 (Polychromatic418967fa.accept_13_1_3_11_1_1289 79 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 232
  (Polychromatic418967fa.accept_21_15_7_1_1_6326 78 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 232 (accept_3_3 77 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 232 (Polychromatic418967fa.accept_14_6_7_8_1_624 76 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 232 (accept_3_3 74 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 232 (Polychromatic418967fa.accept_13_8_3_11_1_3467 73 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 232
  (Polychromatic418967fa.accept_13_7_3_11_1_280 72 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 232 (accept_3_3 71 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 232 (accept_3_3 68 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 232 (Polychromatic418967fa.accept_13_2_3_11_1_1287 67 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 232
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 66 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 232 (accept_3_3 65 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 232 (Polychromatic418967fa.accept_22_20_1_12_1_13879 64 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 232 (accept_3_3 62 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 61 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 232
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 232 (accept_3_3 59 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 232 (accept_3_3 56 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 232
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 232 (accept_3_3 53 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 232 (Polychromatic418967fa.accept_16_4_5_8_1_2425 52 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 232 (accept_3_3 50 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 232 (Polychromatic418967fa.accept_13_10_3_11_1_1923 49 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 232
  (Polychromatic418967fa.accept_14_6_7_8_1_624 48 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 232 (accept_3_3 47 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 232 (accept_3_3 44 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 232 (Polychromatic418967fa.accept_14_1_7_8_1_2063 43 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 232
  (Polychromatic418967fa.accept_17_8_14_11_1_9101 42 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 133 232 (accept_3_3 41 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 133 232 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 133 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 232 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 232 (accept_3_3 38 133 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 232
  (Polychromatic418967fa.accept_17_3_14_11_1_5243 37 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 232 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 232 (accept_3_3 35 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 232 (accept_3_3 32 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 232 (Polychromatic418967fa.accept_20_10_13_12_1_9726 30 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 232 (accept_3_3 29 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 232 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 232 (accept_3_3 26 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 232 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 232 (Polychromatic418967fa.accept_15_9_13_7_1_1361 24 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 232 (accept_3_3 23 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 232 (accept_3_3 20 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 232 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 232 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 232 (accept_3_3 17 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 232 (Polychromatic418967fa.accept_17_16_14_11_1_7836 16
  133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 232 (accept_3_3 14 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 232 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 232 (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 232 (accept_3_3 11 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 232 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 133
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 232 (accept_3_3 8 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 232 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 232 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 232 (accept_3_3 5 133 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 232 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 133 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 232 (accept_3_3 2 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 232 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 133 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 132 232 (Eq.refl Bool.true) (allA_succ_of_gcd 100 132 232 4 25 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 132 232 (Polychromatic418967fa.accept_16_3_4_8_1_3450
  99 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 232 2 49 66 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 232
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 97 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 232 4 24 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 232 (accept_3_3 95 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 232 2 47 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 232 4 23 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 232 2 45 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 232 (accept_3_3 89 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 232 4 22 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 132 232 (Polychromatic418967fa.accept_13_9_2_11_1_1964 87 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 232 2 43 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 232 4 21 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 232 (accept_3_3 83 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 232 2 41 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 232 (Polychromatic418967fa.accept_13_3_2_11_1_1999 81 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 232 4 20 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 232 2 39 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 232 (accept_3_3 77 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 232 4 19 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 232 2 37 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 232 4 18 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 232 (accept_3_3 71 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 232 2 35 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 232 (Polychromatic418967fa.accept_13_4_2_11_1_733 69 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 232 4 17 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 232 2 33 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 232 (accept_3_3 65 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 232 4 16 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 232 (Polychromatic418967fa.accept_14_7_6_8_1_2856 63 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 232 2 31 66 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 232
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 232 4 15 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 232 (accept_3_3 59 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 232 2 29 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 232 4 14 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 232
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 232 2 27 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 232 (accept_3_3 53 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 232 4 13 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 232 2 25 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 232 4 12 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 232 (accept_3_3 47 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 232 2 23 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 232 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 232 4 11 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 232
  (Polychromatic418967fa.accept_13_4_2_11_1_733 43 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 232 2 21 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 232 (accept_3_3 41 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 232 4 10 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 232 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 232 2 19 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 232
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 232 4 9 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 232 (accept_3_3 35 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  132 232 2 17 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 132 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 232 4 8 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 232 (Polychromatic418967fa.accept_9_4_6_7_1_286 31
  132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 232 2 15 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 232 (accept_3_3 29
  132 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 232 4 7 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 232
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 232 2 13 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 232 (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 132 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 232 4 6 33 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 232 (accept_3_3 23 132 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 232 2 11 66 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 232 4 5 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 232 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 232 2 9 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 232 (accept_3_3 17 132 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 232 4 4 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 232 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 132
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 232 2 7 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 232
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 232 4 3 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 232 (accept_3_3 11 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  132 232 2 5 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 232 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 232 4 2 33 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 232 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 132 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 232 2 3 66 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 232 (accept_3_3 5
  132 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 232 4 1 33 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 232
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 232 2 1 66 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 232 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 131 232 (Eq.refl Bool.true) (allA_of_3_1 102 131 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 130
  232 (Eq.refl Bool.true) (allA_succ_of_gcd 102 130 232 2 51 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 130 232 (accept_3_3 101 130 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 130 232 2 50 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 130 232 (Polychromatic418967fa.accept_23_7_15_2_1_13869 99 130 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 130 232 2 49 65 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 130 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 97 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 130 232 2 48 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 130 232 (accept_3_3 95 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 130 232 2 47 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 93 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 232 2 46 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 130 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 91 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 130 232 2 45 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 130 232 (accept_3_3 89 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 130 232 2 44 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 232 2 43 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 130 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 130 232 2 42 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 130 232 (accept_3_3 83 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 232 2 41 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 232 (Polychromatic418967fa.accept_14_11_4_8_1_664 81 130 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 232 2 40 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 232 2 39 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 232 (accept_3_3 77 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 232 2 38 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 232 2 37 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 232 2 36 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 232 (accept_3_3 71 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 232 2 35 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 232 2 34 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 232 2 33 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 232 (accept_3_3 65 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 232 2 32 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 232 (Polychromatic418967fa.accept_15_3_10_7_1_2196 63 130 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 232 2 31 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 61 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 232 2 30 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 232 (accept_3_3 59 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 232 2 29 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 232 2 28 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 232 2 27 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 232 (accept_3_3 53 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 232 2 26 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 232 2 25 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 232 2 24 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 232 (accept_3_3 47 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 232 2 23 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 232 2 22 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 232
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 232 2 21 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 232 (accept_3_3 41 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 232 2 20 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 232 2 19 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 232
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 232 2 18 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 232 (accept_3_3 35 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 232 2 17 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 232 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 232 2 16 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 232
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 232 2 15 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 232 (accept_3_3 29 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 232 2 14 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 232 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 130 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 232 2 13 65 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 232 2 12 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 232 (accept_3_3 23 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 232 2 11 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 232 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 232 2 10 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 232
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 232 2 9 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 232 (accept_3_3 17 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 232 2 8 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 232 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 232 2 7 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 232
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 232 2 6 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 130 232 (accept_3_3 11 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 232 2 5 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 232 (Polychromatic418967fa.accept_19_9_16_4_1_5584 9 130 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 232 2 4 65 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 232
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 232 2 3 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 232 (accept_3_3 5 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  232 2 2 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 232 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 232 2 1 65 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 232 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 129 232 (Eq.refl Bool.true) (allA_succ_of_accept 103 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 102 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 129 232 (accept_3_3 101 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 129 232 (Polychromatic418967fa.accept_20_19_9_12_1_9740 99 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 232 (accept_3_3 98 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 96 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 129 232 (accept_3_3 95 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 129 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 232 (accept_3_3 92 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 129 232 (accept_3_3 89 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 129 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 232 (accept_3_3 86 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 232
  (Polychromatic418967fa.accept_16_4_1_8_1_835 84 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 232 (accept_3_3 83 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 232 (accept_3_3 80 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 232 (accept_3_3 77 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 232 (accept_3_3 74 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 232
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 232 (accept_3_3 71 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 129 232 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 232 (accept_3_3 68 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 232
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 232 (accept_3_3 65 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 232 (Polychromatic418967fa.accept_16_15_1_8_1_1585 63 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 232 (accept_3_3 62 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 232
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 232 (accept_3_3 59 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 232 (accept_3_3 56 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 232
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 232 (accept_3_3 53 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 232 (Polychromatic418967fa.accept_16_4_1_8_1_835 52 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 232 (accept_3_3 50 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 232
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 232 (accept_3_3 47 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 232 (Polychromatic418967fa.accept_22_1_19_12_1_13878 45 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 232 (accept_3_3 44 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 232 (accept_3_3 41 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 232 (accept_3_3 38 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 232
  (Polychromatic418967fa.accept_13_10_12_11_1_731 36 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 232 (accept_3_3 35 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 232 (Polychromatic418967fa.accept_23_11_14_2_1_13877 34 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 232 (Polychromatic418967fa.accept_7_5_3_1_1_424
  33 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 232 (accept_3_3 32
  129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 232 (accept_3_3 29 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 129 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 232 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  27 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 232 (accept_3_3 26
  129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 129 232 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 232 (accept_3_3 23 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 232 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 232 (Polychromatic418967fa.accept_10_1_9_2_1_45
  21 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 232 (accept_3_3 20
  129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 232 (accept_3_3 17 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 232 (Polychromatic418967fa.accept_9_6_3_7_1_580
  15 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 232 (accept_3_3 14
  129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 232
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 129 232 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 232 (accept_3_3 11 129 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 232 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 232 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 232 (accept_3_3 8 129
  232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 232
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 232 (accept_3_3 5 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 232 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 232 (Polychromatic418967fa.accept_17_3_10_11_1_7848 3 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 232 (accept_3_3 2 129 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 232 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 128 232 (Eq.refl Bool.true) (allA_of_3_1 105 128 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 127 232 (Eq.refl Bool.true) (allA_succ_of_accept 105 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 232 (accept_3_3 104 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 232 (accept_3_3 101 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 232 (Polychromatic418967fa.accept_14_2_1_8_1_650 100 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 232 (accept_3_3 98 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 232 (Polychromatic418967fa.accept_16_1_15_8_1_2411 97 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 232 (accept_3_3 95 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 232 (accept_3_3 92 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 232 (Polychromatic418967fa.accept_14_7_1_8_1_2873 91 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 232 (Polychromatic418967fa.accept_13_12_10_11_1_1279 90 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 232 (accept_3_3 89 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 232 (Polychromatic418967fa.accept_25_13_2_7_1_13876 88 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 232 (accept_3_3 86 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 232 (accept_3_3 83 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 82 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 232 (accept_3_3 80 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 79 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 232 (accept_3_3 77 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 232 (accept_3_3 74 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 232 (Polychromatic418967fa.accept_11_7_6_1_1_2182 73 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 232 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 232 (accept_3_3 71 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 232 (accept_3_3 68 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 232 (accept_3_3 65 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 232 (accept_3_3 62 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 232 (Polychromatic418967fa.accept_18_7_1_16_1_578 61 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 232 (accept_3_3 59 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 232 (accept_3_3 56 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 232 (accept_3_3 53 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 232 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 232 (accept_3_3 50 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 232 (accept_3_3 47 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 232 (accept_3_3 44 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 232 (Polychromatic418967fa.accept_13_4_10_11_1_1908 43 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 232 (accept_3_3 41 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 232 (accept_3_3 38 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 232 (Polychromatic418967fa.accept_14_9_1_8_1_2849 37 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 232 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 232 (accept_3_3 35 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 232 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 232 (accept_3_3 32 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 232 (accept_3_3 29 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 232 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 127 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 232 (accept_3_3 26 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 232 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 232 (accept_3_3 23 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 232 (accept_3_3 20 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 232 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 232 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 232 (accept_3_3 17 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 232 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 127
  232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 232 (accept_3_3 14 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 232 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 232 (accept_3_3 11 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 232 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 232 (accept_3_3 8 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 232 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 232 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 232 (accept_3_3 5 127 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 232 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 232
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 232 (accept_3_3 2 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 232 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 127 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 126 232 (Eq.refl Bool.true) (allA_succ_of_gcd 106 126 232 2 53 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 232
  (Polychromatic418967fa.accept_11_6_5_1_1_586 105 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 232 2 52 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 232 (Polychromatic418967fa.accept_15_13_6_7_1_1369 103 126 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 126 232 2 51 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 126 232 (accept_3_3 101 126 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 232 2 50 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 232
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 232 2 49 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 232 (Polychromatic418967fa.accept_19_2_12_4_1_4193 97 126 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 232 2 48 63 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 232 (accept_3_3 95 126 232
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 232 2 47 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 232
  (Polychromatic418967fa.accept_12_9_6_4_1_402 93 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 232 2 46 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 91 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 126 232 2 45 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 232 (accept_3_3 89 126 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 232 2 44 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400
  87 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 232 2 43 63 116
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 232
  (Polychromatic418967fa.accept_13_7_9_11_1_705 85 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 232 2 42 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 232 (accept_3_3 83 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 232 2 41 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 126 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 81 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 232 2 40 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 232
  (Polychromatic418967fa.accept_13_1_9_11_1_703 79 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 232 2 39 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 232 (accept_3_3 77 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 232 2 38 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 232 2 37 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 232
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 73 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 232 2 36 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 232 (accept_3_3 71 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 232 2 35 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 232 2 34 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 232
  (Polychromatic418967fa.accept_13_2_9_11_1_258 67 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 232 2 33 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 232 (accept_3_3 65 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 232 2 32 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 232 2 31 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 232 2 30 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 232 (accept_3_3 59 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 232 2 29 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 232 2 28 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 232
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 55 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 126 232 2 27 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 126 232 (accept_3_3 53 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 232 2 26 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 232 2 25 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 232
  (Polychromatic418967fa.accept_19_11_12_4_1_8455 49 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 232 2 24 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 232 (accept_3_3 47 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 232 2 23 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 232 2 22 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 232
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 232 2 21 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 232 (accept_3_3 41 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 232 2 20 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 232 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 232 2 19 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 232
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 37 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 232 2 18 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 232 (accept_3_3 35 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 232 2 17 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 232 2 16 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 232
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 232 2 15 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 232 (accept_3_3 29 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 232 2 14 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 232 2 13 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 232
  (Polychromatic418967fa.accept_19_6_12_4_1_8516 25 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 232 2 12 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 232 (accept_3_3 23 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 232 2 11 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 232 2 10 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 232
  (Polychromatic418967fa.accept_22_19_16_12_1_7588 19 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 232 2 9 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 232 (accept_3_3 17 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 232 2 8 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 232 2 7 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 232
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 232 2 6 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 232 (accept_3_3 11 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 232 2 5 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 232 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 232 2 4 63 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 232
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 232 2 3 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 232 (accept_3_3 5 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  232 2 2 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 232 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 232 2 1 63 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 232 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 126 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 125 232 (Eq.refl Bool.true) (allA_of_3_1 108 125 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 124 232 (Eq.refl Bool.true) (allA_succ_of_gcd 108 124 232 4 27 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 124 232 (accept_3_3 107 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 124 232 2 53 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 124 232 (Polychromatic418967fa.accept_13_1_7_11_1_702
  105 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 124 232 4 26 31 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 124 232
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 103 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 124 232 2 51 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 124 232 (accept_3_3 101 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 124 232 4 25 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 124 232 (Polychromatic418967fa.accept_16_3_12_8_1_808 99 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 124 232 2 49 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 124 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 97 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 124 232 4 24 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 124 232 (accept_3_3 95 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 124 232 2 47 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 124 232 (Polychromatic418967fa.accept_15_3_4_7_1_1352 93 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 124 232 4 23 31 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 124 232
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 91 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 124 232 2 45 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 124 232 (accept_3_3 89 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 124 232 4 22 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 124 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 124 232 2 43 62 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 232
  (Polychromatic418967fa.accept_15_10_4_7_1_3127 85 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 124 232 4 21 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 124 232 (accept_3_3 83 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 124 232 2 41 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 124 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 232 4 20 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 232
  (Polychromatic418967fa.accept_11_2_3_1_1_244 79 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 232 2 39 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 232 (accept_3_3 77 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 232 4 19 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 232 (Polychromatic418967fa.accept_16_11_12_8_1_1592 75 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 232 2 37 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 232 4 18 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 232 (accept_3_3 71 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 232 2 35 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 232 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 232 4 17 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 232
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 232 2 33 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 232 (accept_3_3 65 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 232 4 16 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 232 (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 232 2 31 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 232
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 232 4 15 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 232 (accept_3_3 59 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 232 2 29 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 232 4 14 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 232 2 27 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 232 (accept_3_3 53 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 232 4 13 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 232 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 232 2 25 62 116 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 232
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 49 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 232 4 12 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 232 (accept_3_3 47 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 232 2 23 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 232 4 11 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 232
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 232 2 21 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 232 (accept_3_3 41 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 232 4 10 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 232 2 19 62 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 232
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 232 4 9 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 232 (accept_3_3 35 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 232 2 17 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 232 (Polychromatic418967fa.accept_15_3_4_7_1_1352 33 124 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 232 4 8 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 232 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 232 2 15 62 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 232 (accept_3_3 29
  124 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 232 4 7 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 232 2 13 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 232 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 232 4 6 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 232 (accept_3_3 23 124 232 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 232 2 11 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 232 (Polychromatic418967fa.accept_16_5_12_8_1_2521
  21 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 232 4 5 31 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 232
  (Polychromatic418967fa.accept_16_3_12_8_1_808 19 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 232 2 9 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 232 (accept_3_3 17 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 232 4 4 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 124 232 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 124 232 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 232 2 7 62 116 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 232
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 232 4 3 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 232 (accept_3_3 11 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 232 2 5 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 232 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 124 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 232 4 2 31 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 232 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 232
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 232 2 3 62 116 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 232 (accept_3_3 5
  124 232 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 232 4 1 31 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 232
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 232 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 232 2 1 62 116 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 232 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 124 232 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  232)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_232_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


