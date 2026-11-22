-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch229
-- name    : Polychromatic418967fa_Branch229
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:26:24.825151+00:00
-- url     : https://prove2.me/theorems/99ba2391-b2b6-4963-8a5f-e329c6bd4ba8
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch229_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_229 : allB 229 229 :=
  allB_succ' 2 228 229 (Eq.refl Bool.true) (allA_succ_of_accept 1 228 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  228 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 229)) (allB_succ' 3 227 229
  (Eq.refl Bool.true) (allA_of_3_1 3 227 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 226 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 229 (accept_3_3 2 226 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 226 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 229)))) (allB_succ' 5 225 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 225 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 225 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 229 (accept_3_3 2 225 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  225 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 229))))) (allB_succ' 6 224 229
  (Eq.refl Bool.true) (allA_of_3_1 6 224 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 223 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 223 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 229 (accept_3_3 5 223 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 223 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 223 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 229 (accept_3_3 2 223 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 223 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 229))))))) (allB_succ' 8 222 229 (Eq.refl Bool.true) (allA_succ_of_accept 7 222 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 222 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 222 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 229 (accept_3_3 5 222 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 222 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 222 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  222 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 229 (accept_3_3 2 222
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 229 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 222 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 229)))))))) (allB_succ' 9 221 229
  (Eq.refl Bool.true) (allA_of_3_1 9 221 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 220 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 229 (accept_3_3 8 220 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 220 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 229
  (Polychromatic418967fa.accept_15_6_10_4_1_150 6 220 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 220 229 (accept_3_3 5 220 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  220 229 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 220 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 220 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 229 (accept_3_3 2 220 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 220 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 229)))))))))) (allB_succ' 11 219 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 219 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  219 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 229 (accept_3_3 8 219
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 229
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 219 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 219 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 229 (accept_3_3 5 219 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 219 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  219 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 229 (accept_3_3 2 219
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 229 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 219 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 229))))))))))) (allB_succ' 12 218
  229 (Eq.refl Bool.true) (allA_of_3_1 12 218 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 217 229
  (Eq.refl Bool.true) (allA_succ_of_accept 12 217 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 217 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 229 (accept_3_3 11 217 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 217
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 229
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 229 (accept_3_3 8 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 217 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 229 (accept_3_3 5 217 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 217 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 229 (accept_3_3 2 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 217 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 229))))))))))))) (allB_succ' 14 216 229 (Eq.refl Bool.true) (allA_succ_of_accept 13 216 229
  (Polychromatic418967fa.accept_10_3_6_9_1_779 13 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 216 229 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 216 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 229 (accept_3_3 11 216 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 216 229 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 216 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 229
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 216 229 (accept_3_3 8 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  216 229 (Polychromatic418967fa.accept_20_7_16_9_1_4970 7 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 216 229 (Polychromatic418967fa.accept_19_6_7_1_1_2805 6 216 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 229 (accept_3_3 5 216 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 216 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 229
  (Polychromatic418967fa.accept_10_3_6_9_1_779 3 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 216 229 (accept_3_3 2 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  216 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 216 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 216 229)))))))))))))) (allB_succ' 15 215 229 (Eq.refl Bool.true) (allA_of_3_1 15 215 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 214 229 (Eq.refl Bool.true) (allA_succ_of_accept 15 214 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 214 229 (accept_3_3 14 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 214 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 214 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 214 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 214 229 (accept_3_3 11 214 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 214 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 214 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 214 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 229 (accept_3_3 8 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 214 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 229 (accept_3_3 5 214 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 214 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 229 (accept_3_3 2 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 214 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 229)))))))))))))))) (allB_succ' 17 213 229 (Eq.refl Bool.true) (allA_succ_of_accept 16 213
  229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 213 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 213 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 229 (accept_3_3 14 213 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 213 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 213 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 229 (accept_3_3 11 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 213 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 229 (accept_3_3 8 213 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 213 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 229
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 229 (accept_3_3 5 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 213 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 229 (accept_3_3 2 213 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 213 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 229))))))))))))))))) (allB_succ' 18 212 229 (Eq.refl
  Bool.true) (allA_of_3_1 18 212 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 211 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 211 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 229 (accept_3_3 17 211 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 211 229 (Polychromatic418967fa.accept_17_16_7_8_1_7638 16 211 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 229 (accept_3_3 14 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 211 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 229 (accept_3_3 11 211 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 229
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 229 (accept_3_3 8 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 229 (accept_3_3 5 211 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 211 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 229 (accept_3_3 2 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 229 (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 211 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 229))))))))))))))))))) (allB_succ' 20 210 229 (Eq.refl Bool.true) (allA_succ_of_accept 19
  210 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 210 229 (Polychromatic418967fa.accept_23_18_3_22_1_10551 18 210 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 229 (accept_3_3 17 210 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 210 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 210 229 (accept_3_3 14 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 210 229 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 210 229 (Polychromatic418967fa.accept_24_12_18_13_1_13726 12 210 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 229 (accept_3_3 11 210 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 210 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 229
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 210 229 (accept_3_3 8 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  210 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 210 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 210 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 229 (accept_3_3 5 210 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 229 (Polychromatic418967fa.accept_23_4_3_22_1_13725 4 210 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 210 229 (accept_3_3 2 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  210 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 210 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 229)))))))))))))))))))) (allB_succ' 21 209 229 (Eq.refl Bool.true) (allA_of_3_1 21 209 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 208 229 (Eq.refl Bool.true) (allA_succ_of_accept 21 208 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 229 (accept_3_3 20 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 229 (Polychromatic418967fa.accept_17_1_4_8_1_5049 18 208 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 229 (accept_3_3 17 208 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 208 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 229 (accept_3_3 14 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 229 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 208 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 208 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 229 (accept_3_3 11 208 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 208 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 229 (accept_3_3 8 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 208 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 229 (accept_3_3 5 208 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 208 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 229 (accept_3_3 2 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 208 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 229)))))))))))))))))))))) (allB_succ' 23 207 229 (Eq.refl Bool.true) (allA_succ_of_accept 22
  207 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 207 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 229 (accept_3_3 20 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 229 (Polychromatic418967fa.accept_27_19_18_13_1_13724 19
  207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 207 229 (accept_3_3 17 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 207 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 207 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 229 (accept_3_3 14 207 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 229 (accept_3_3 11 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 207 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 229 (accept_3_3 8 207 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 229 (accept_3_3 5 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 229 (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 229 (accept_3_3 2 207 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 207 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207 229))))))))))))))))))))))) (allB_succ' 24
  206 229 (Eq.refl Bool.true) (allA_of_3_1 24 206 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 205 229
  (Eq.refl Bool.true) (allA_succ_of_accept 24 205 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 205 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 229 (accept_3_3 23 205 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 205
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 229 (accept_3_3 20 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 229 (accept_3_3 17 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 205 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 229 (accept_3_3 14 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 229 (accept_3_3 11 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 205 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 229 (accept_3_3 8 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 229 (accept_3_3 5 205 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 205 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 229 (accept_3_3 2 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 205 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 229))))))))))))))))))))))))) (allB_succ' 26 204 229 (Eq.refl Bool.true) (allA_succ_of_accept
  25 204 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 204 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 204 229 (accept_3_3 23 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 229 (Polychromatic418967fa.accept_20_2_4_9_1_9524 22 204 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 204 229 (accept_3_3 20 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 204 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 204 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 229 (accept_3_3 17 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 204 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 229
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 204 229 (accept_3_3 14 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 204 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 204 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 229 (accept_3_3 11 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 204 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 204 229 (accept_3_3 8 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  204 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 204 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 229 (accept_3_3 5 204 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 204 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 204 229 (accept_3_3 2 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  204 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 204 229)))))))))))))))))))))))))) (allB_succ' 27 203 229 (Eq.refl Bool.true) (allA_of_3_1 27 203
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 202 229 (Eq.refl Bool.true) (allA_succ_of_accept 27 202
  229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 202 229 (accept_3_3 26 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 202 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 202 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 202 229 (accept_3_3 23 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 202 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 202 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 202 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 202 229 (accept_3_3 20 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 202 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 202 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 202 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 202 229 (accept_3_3 17 202 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 202 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 202 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 202 229 (accept_3_3 14 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 202 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 202 229 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 202 229 (accept_3_3 11 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 202
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 202 229 (accept_3_3 8 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  202 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 202 229 (Polychromatic418967fa.accept_17_6_15_8_1_1714 6 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 229 (accept_3_3 5 202 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 202 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 202 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 202 229 (accept_3_3 2 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  202 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 202 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 202 229)))))))))))))))))))))))))))) (allB_succ' 29 201 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 201 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 201
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 229 (accept_3_3 26 201
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 229
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 201 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 229 (accept_3_3 23 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 201 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 201 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 229
  (Polychromatic418967fa.accept_23_21_17_22_1_13723 21 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 229 (accept_3_3 20 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 201
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 229 (accept_3_3 17 201
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 229
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 201 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 229 (accept_3_3 14 201 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 201 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 201 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 229 (accept_3_3 11 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 201 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 201 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 229 (accept_3_3 8 201 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 201 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 229 (accept_3_3 5 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 201 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 229 (accept_3_3 2 201 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 201 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 229))))))))))))))))))))))))))))) (allB_succ' 30 200
  229 (Eq.refl Bool.true) (allA_of_3_1 30 200 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 199 229
  (Eq.refl Bool.true) (allA_succ_of_accept 30 199 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 229 (accept_3_3 29 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 229 (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 199
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 229
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 229 (accept_3_3 26 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 199 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 229 (accept_3_3 23 199 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 229 (accept_3_3 20 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 229 (Polychromatic418967fa.accept_23_19_15_22_1_8770 19 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 229 (accept_3_3 17 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 199 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 229 (accept_3_3 14 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 229 (Polychromatic418967fa.accept_20_13_19_9_1_10976 13 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 229 (accept_3_3 11 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 229 (accept_3_3 8 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 229 (accept_3_3 5 199 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 229 (Polychromatic418967fa.accept_17_4_12_8_1_3833 4 199 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 229 (accept_3_3 2 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 199 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 229))))))))))))))))))))))))))))))) (allB_succ' 32 198 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 229 (Polychromatic418967fa.accept_19_11_8_1_1_801 30 198
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 198 229 (accept_3_3 29 198
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 229
  (Polychromatic418967fa.accept_19_9_8_1_1_11103 28 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 229 (accept_3_3 26 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 198 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 198 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 229 (Polychromatic418967fa.accept_7_3_2_5_1_147
  24 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 198 229 (accept_3_3 23
  198 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 198 229
  (Polychromatic418967fa.accept_13_9_3_8_1_573 22 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 198 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 229 (accept_3_3 20 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 229 (Polychromatic418967fa.accept_7_4_2_5_1_527
  18 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 229 (accept_3_3 17
  198 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 229
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 229 (accept_3_3 14 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 198 229 (Polychromatic418967fa.accept_19_13_8_1_1_8290 13 198 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 229
  (Polychromatic418967fa.accept_19_12_8_1_1_11059 12 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 198 229 (accept_3_3 11 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 198 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 198 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 229 (accept_3_3 8 198 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 229
  (Polychromatic418967fa.accept_25_6_23_4_1_13722 6 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 229 (accept_3_3 5 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 198 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 229 (accept_3_3 2 198 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 198 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 229)))))))))))))))))))))))))))))))) (allB_succ' 33
  197 229 (Eq.refl Bool.true) (allA_of_3_1 33 197 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 196 229
  (Eq.refl Bool.true) (allA_succ_of_accept 33 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 229 (accept_3_3 32 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 196
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 229 (accept_3_3 29 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 196 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 229 (accept_3_3 26 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 229 (accept_3_3 23 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 229 (accept_3_3 20 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 229
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 229 (accept_3_3 17 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 229 (Polychromatic418967fa.accept_17_16_9_8_1_5063 16 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 229 (accept_3_3 14 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 229 (accept_3_3 11 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 229 (accept_3_3 8 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 229 (accept_3_3 5 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 229 (Polychromatic418967fa.accept_21_4_7_19_1_13687 4 196 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 229 (accept_3_3 2 196 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 196 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 229)))))))))))))))))))))))))))))))))) (allB_succ' 35
  195 229 (Eq.refl Bool.true) (allA_succ_of_accept 34 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 195 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 229 (accept_3_3 32 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 229 (accept_3_3 29 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 229
  (Polychromatic418967fa.accept_25_2_20_4_1_13721 27 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 229 (accept_3_3 26 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 195 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 195
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 229 (accept_3_3 23 195
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2
  22 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 229 (accept_3_3 20 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 229 (accept_3_3 17 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 229 (accept_3_3 14 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 229 (Polychromatic418967fa.accept_21_13_6_19_1_4489 13 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 195 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 229 (accept_3_3 11 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 195 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 229 (accept_3_3 8 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 229 (accept_3_3 5 195 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 229 (accept_3_3 2 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 195 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 229))))))))))))))))))))))))))))))))))) (allB_succ' 36 194 229 (Eq.refl Bool.true)
  (allA_of_3_1 36 194 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 193 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 193 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 193 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 229 (accept_3_3 35 193 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 193 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 193 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 229
  (Polychromatic418967fa.accept_21_12_4_19_1_4526 33 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 193 229 (accept_3_3 32 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 193 229 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 193 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 193 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 229 (accept_3_3 29 193 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 229 (Polychromatic418967fa.accept_8_4_1_5_1_186
  28 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 229 (accept_3_3 26 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 193 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 229 (accept_3_3 23 193 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 193 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 229
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 229 (accept_3_3 20 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 229 (Polychromatic418967fa.accept_21_18_4_19_1_1838 18 193 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 229 (accept_3_3 17 193 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 193 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 229 (accept_3_3 14 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 193 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 229 (accept_3_3 11 193 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 193 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 229 (accept_3_3 8 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 229 (Polychromatic418967fa.accept_21_7_4_19_1_4525 7 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 193 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 229 (accept_3_3 5 193 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 193 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 229
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 229 (accept_3_3 2 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 193 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 229))))))))))))))))))))))))))))))))))))) (allB_succ' 38 192 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 192 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 192 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 192 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 229 (accept_3_3 35 192 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 229 (Polychromatic418967fa.accept_9_7_3_4_1_218
  34 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 192 229 (accept_3_3 32 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 192 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 192 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 229 (accept_3_3 29 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 229
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 192 229 (accept_3_3 26 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 192 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 192 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 229 (accept_3_3 23 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 229
  (Polychromatic418967fa.accept_10_1_2_9_1_152 21 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 229 (accept_3_3 20 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 192 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 229 (accept_3_3 17 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 192 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 192 229 (accept_3_3 14 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 192 229 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 192 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 229 (accept_3_3 11 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 192 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 229 (accept_3_3 8 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  192 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 229 (accept_3_3 5 192 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 229 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 192 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 229
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 192 229 (accept_3_3 2 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  192 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 192 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192 229)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 191 229 (Eq.refl Bool.true)
  (allA_of_3_1 39 191 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 190 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 190 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 229 (accept_3_3 38 190 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 190 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 229
  (Polychromatic418967fa.accept_15_6_10_4_1_150 36 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 190 229 (accept_3_3 35 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 190 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 190 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 229 (accept_3_3 32 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 190 229 (accept_3_3 29 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 190 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 190 229 (accept_3_3 26 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 190 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 190 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 190 229 (accept_3_3 23 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 229 (accept_3_3 20 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 229 (accept_3_3 17 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 229 (accept_3_3 14 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 229 (accept_3_3 11 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 229 (accept_3_3 8 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 229 (accept_3_3 5 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 190 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 229 (accept_3_3 2 190 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 190 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 229))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 189 229 (Eq.refl Bool.true) (allA_succ_of_accept 40 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57
  40 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 229 (accept_3_3 38 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 229 (accept_3_3 35 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 189 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 229
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 189 229 (accept_3_3 32 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 189 229 (Polychromatic418967fa.accept_19_12_18_1_1_12336 31 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 229 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 229 (accept_3_3 29 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 189 229 (accept_3_3 26 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 189 229 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 229 (Polychromatic418967fa.accept_16_8_13_5_1_1395 24 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 229 (accept_3_3 23 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 189 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 229
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 229 (accept_3_3 20 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 229 (Polychromatic418967fa.accept_25_19_14_4_1_13709 19 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 229 (accept_3_3 17 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 229
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 229 (accept_3_3 14 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 229 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 189 229 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 229 (accept_3_3 11 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 189 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 229
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 229 (accept_3_3 8 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 189 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 229 (accept_3_3 5 189 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 229 (accept_3_3 2 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 189 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 229))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 188 229 (Eq.refl Bool.true)
  (allA_of_3_1 42 188 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 187 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 187 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 229 (accept_3_3 41 187 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 187 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 229 (accept_3_3 38 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 229 (accept_3_3 35 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 187 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 229 (accept_3_3 32 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 229 (Polychromatic418967fa.accept_24_7_19_13_1_6703 31 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 229 (accept_3_3 29 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 229
  (Polychromatic418967fa.accept_13_1_5_8_1_207 27 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 229 (accept_3_3 26 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 229 (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 229 (accept_3_3 23 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 229 (accept_3_3 20 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 229 (accept_3_3 17 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 229 (accept_3_3 14 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 229 (Polychromatic418967fa.accept_19_13_16_1_1_4044 13 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 229 (accept_3_3 11 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 229
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 229 (accept_3_3 8 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 229 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 229 (accept_3_3 5 187 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 229 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 187 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 229 (accept_3_3 2 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 187 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 229))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 186 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 229 (Polychromatic418967fa.accept_19_4_15_1_1_2819 42 186
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 229 (accept_3_3 41 186
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 229
  (Polychromatic418967fa.accept_15_10_6_4_1_1256 40 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 229 (accept_3_3 38 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 186 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36
  186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 229 (accept_3_3 35
  186 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 186 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 229 (accept_3_3 32 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 229 (Polychromatic418967fa.accept_7_2_4_5_1_313
  30 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 229 (accept_3_3 29
  186 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 229
  (Polychromatic418967fa.accept_9_1_6_4_1_49 28 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 229 (accept_3_3 26 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 186 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 229
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 186 229 (accept_3_3 23 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 186 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 229 (accept_3_3 20 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 229
  (Polychromatic418967fa.accept_22_18_10_9_1_13720 18 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 229 (accept_3_3 17 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 186 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 229 (accept_3_3 14 186 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 229 (Polychromatic418967fa.accept_7_6_4_5_1_314
  13 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 229 (accept_3_3 11 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 229 (accept_3_3 8 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 229 (accept_3_3 5 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 229 (Polychromatic418967fa.accept_19_4_15_1_1_2819 4 186 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 229 (accept_3_3 2 186 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 186 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 229))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 185 229 (Eq.refl Bool.true) (allA_of_3_1 45 185 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 184 229 (Eq.refl Bool.true) (allA_succ_of_accept 45 184 229 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 229 (accept_3_3 44
  184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 229
  (Polychromatic418967fa.accept_10_3_4_9_1_15 43 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 184 229 (Polychromatic418967fa.accept_20_2_4_9_1_9524 42 184 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 184 229 (accept_3_3 41 184 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 184 229 (Polychromatic418967fa.accept_17_6_14_8_1_3858 40 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 184 229 (accept_3_3 38 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 184 229 (Polychromatic418967fa.accept_19_18_13_1_1_9735 37 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 184 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 184 229 (accept_3_3 35 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 184 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 184
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 184 229 (accept_3_3 32 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 184 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 184 229 (Polychromatic418967fa.accept_24_6_16_13_1_6762 30 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 229 (accept_3_3 29 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 184
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 184 229 (accept_3_3 26 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 184 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 229 (accept_3_3 23 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 184 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 229 (accept_3_3 20 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 229 (accept_3_3 17 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 229 (Polychromatic418967fa.accept_17_16_14_8_1_7608 16 184 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 229 (accept_3_3 14 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 229 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 229 (accept_3_3 11 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 184 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 229 (accept_3_3 8 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 229 (accept_3_3 5 184 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 184 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 229 (accept_3_3 2 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 229 (Polychromatic418967fa.accept_21_1_16_19_1_3134 1 184 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 229)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 183 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 183 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 183 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 183 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 229 (accept_3_3 44 183 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 229 (Polychromatic418967fa.accept_9_7_3_4_1_218
  43 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 229 (accept_3_3 41 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 229 (accept_3_3 38 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 229
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 229 (accept_3_3 35 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 229 (accept_3_3 32 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 229 (accept_3_3 29 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 229 (accept_3_3 26 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 229 (accept_3_3 23 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 229 (accept_3_3 20 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 183 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 229 (accept_3_3 17 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 229 (accept_3_3 14 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 229
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 229 (accept_3_3 11 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 229 (accept_3_3 8 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 229 (accept_3_3 5 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 229 (accept_3_3 2 183 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 183 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 229)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 182 229 (Eq.refl Bool.true) (allA_of_3_1 48 182 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 181 229 (Eq.refl Bool.true) (allA_succ_of_accept 48 181 229 (Polychromatic418967fa.accept_9_3_1_4_1_216
  48 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 229 (accept_3_3 47
  181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 181 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 181 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 229 (accept_3_3 44 181 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 181 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 229 (Polychromatic418967fa.accept_9_6_1_4_1_474
  42 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 229 (accept_3_3 41
  181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 229
  (Polychromatic418967fa.accept_11_7_5_9_1_884 40 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 181 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 181 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 229 (accept_3_3 38 181 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 181 229 (Polychromatic418967fa.accept_21_16_13_19_1_6035 37 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 181 229 (accept_3_3 35 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 181 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 181 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 229 (accept_3_3 32 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 229 (accept_3_3 29 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 229 (accept_3_3 26 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 181 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 229 (accept_3_3 23 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 229 (accept_3_3 20 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 229 (Polychromatic418967fa.accept_17_2_11_8_1_2726 19 181 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 229 (accept_3_3 17 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 229 (accept_3_3 14 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 229 (Polychromatic418967fa.accept_19_13_10_1_1_8236 13 181 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 181 229 (accept_3_3 11 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 181 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 229 (accept_3_3 8 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 229 (accept_3_3 5 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 181 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 229 (accept_3_3 2 181 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 181 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 229)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 180 229 (Eq.refl Bool.true) (allA_succ_of_accept 49 180 229 (Polychromatic418967fa.accept_8_1_4_5_1_48
  49 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 180 229
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 180 229 (accept_3_3 47 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 180 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 180 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 180 229 (accept_3_3 44 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 229 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 229
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 42 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 180 229 (accept_3_3 41 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 180 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 180 229 (Polychromatic418967fa.accept_21_18_12_19_1_10725 39 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 180 229 (accept_3_3 38 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 229 (Polychromatic418967fa.accept_22_15_4_9_1_13719 37 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 229
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 180 229 (accept_3_3 35 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 180 229 (Polychromatic418967fa.accept_23_11_19_22_1_12042 34 180 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 180 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 33
  180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 229 (accept_3_3 32
  180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 229
  (Polychromatic418967fa.accept_14_3_12_5_1_153 31 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 180 229 (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 180 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 229 (accept_3_3 29 180 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 180 229 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 180 229
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 180 229 (accept_3_3 26 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 180 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 180 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 229 (accept_3_3 23 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 229 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 229
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 180 229 (accept_3_3 20 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 180 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 180 229 (Polychromatic418967fa.accept_21_18_12_19_1_10725 18 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 229 (accept_3_3 17 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 229 (Polychromatic418967fa.accept_13_3_11_8_1_1094 16 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 180 229
  (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 180 229 (accept_3_3 14 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 180 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 180 229 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 229 (accept_3_3 11 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 180 229 (accept_3_3 8 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  180 229 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 180 229 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 229 (accept_3_3 5 180 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 229 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 180
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 229
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 229 (accept_3_3 2 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  180 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 180 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 229)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 179 229 (Eq.refl
  Bool.true) (allA_of_3_1 51 179 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 178 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 178 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 178 229 (accept_3_3 50 178 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 178 229 (Polychromatic418967fa.accept_21_7_10_19_1_10739 49 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 178 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 178 229 (accept_3_3 47 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 178 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 178 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 178 229 (accept_3_3 44 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 178 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 178 229 (accept_3_3 41 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 178 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 178 229 (accept_3_3 38 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 178 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 178 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 178 229 (accept_3_3 35 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 178 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 178 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 229 (accept_3_3 32 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 178 229 (accept_3_3 29 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 178 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 229 (accept_3_3 26 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 178 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 178 229 (accept_3_3 23 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 229 (accept_3_3 20 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 229
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 229 (accept_3_3 17 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 229 (accept_3_3 14 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 229 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 178 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 229 (accept_3_3 11 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 229 (accept_3_3 8 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 229 (accept_3_3 5 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 178 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 229 (accept_3_3 2 178 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 178 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  229)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 177 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 229 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 177
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 229 (accept_3_3 50 177
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 229
  (Polychromatic418967fa.accept_14_7_9_5_1_529 49 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 177 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 229 (accept_3_3 47 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 229 (Polychromatic418967fa.accept_7_3_2_5_1_147
  45 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 229 (accept_3_3 44
  177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 177 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 229 (accept_3_3 41 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 229 (Polychromatic418967fa.accept_7_4_2_5_1_527
  39 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 229 (accept_3_3 38
  177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 229
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 177 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 229 (accept_3_3 35 177 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 229
  (Polychromatic418967fa.accept_17_16_7_8_1_7638 33 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 229 (accept_3_3 32 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 229 (accept_3_3 29 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 229 (accept_3_3 26 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 229 (accept_3_3 23 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 177 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 229 (accept_3_3 20 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 229 (accept_3_3 17 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 229 (accept_3_3 14 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 229 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 229 (accept_3_3 11 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 177 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 229 (accept_3_3 8 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 229 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 229 (accept_3_3 5 177 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 229 (accept_3_3 2 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 177 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 229))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 176 229 (Eq.refl
  Bool.true) (allA_of_3_1 54 176 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 175 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 175 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 229 (accept_3_3 53 175 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 175 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 229 (accept_3_3 50 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 229 (Polychromatic418967fa.accept_16_1_15_5_1_708 49 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 229 (Polychromatic418967fa.accept_19_10_4_1_1_4018 48 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 229 (accept_3_3 47 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 175 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 229
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 229 (accept_3_3 44 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 229 (accept_3_3 41 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 229 (accept_3_3 38 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 229 (Polychromatic418967fa.accept_13_11_6_8_1_1121 37 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 229 (accept_3_3 35 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 175 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 229
  (Polychromatic418967fa.accept_16_1_15_5_1_708 33 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 229 (accept_3_3 32 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 229 (accept_3_3 29 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 229
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 229 (accept_3_3 26 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 229 (Polychromatic418967fa.accept_20_5_15_9_1_9446 25 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 229 (accept_3_3 23 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 229 (accept_3_3 20 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 229 (accept_3_3 17 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 229
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 229 (accept_3_3 14 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 229 (accept_3_3 11 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 229
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 229 (accept_3_3 8 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 229 (accept_3_3 5 175 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 175 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 229
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 229 (accept_3_3 2 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 175 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 229))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 174 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 174 229
  (Polychromatic418967fa.accept_19_16_3_1_1_5389 54 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 174 229 (accept_3_3 53 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 174 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 174 229 (accept_3_3 50 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 174 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 174 229 (accept_3_3 47 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 174 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 174 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 174 229 (accept_3_3 44 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 174 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 174 229 (accept_3_3 41 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 174 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 229 (accept_3_3 38 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 174 229 (accept_3_3 35 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 174 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 174 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 229 (accept_3_3 32 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 229
  (Polychromatic418967fa.accept_17_13_4_8_1_3830 30 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 174 229 (accept_3_3 29 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 174 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 229 (accept_3_3 26 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 174 229 (accept_3_3 23 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 174 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 174 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 229 (accept_3_3 20 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 229 (accept_3_3 17 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 229 (accept_3_3 14 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 229
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 174 229 (accept_3_3 11 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 174 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 174 229 (Polychromatic418967fa.accept_16_9_14_5_1_2239 9 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 229 (accept_3_3 8 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 229 (accept_3_3 5 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 174 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 229 (accept_3_3 2 174 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 174 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 173 229 (Eq.refl Bool.true) (allA_of_3_1 57
  173 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 172 229 (Eq.refl Bool.true) (allA_succ_of_accept 57
  172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 172 229 (accept_3_3 56 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 172 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 172 229 (Polychromatic418967fa.accept_21_12_4_19_1_4526 54 172
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 229 (accept_3_3 53 172
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 172 229
  (Polychromatic418967fa.accept_9_7_1_4_1_217 52 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 172 229 (accept_3_3 50 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 172 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 172 229 (Polychromatic418967fa.accept_7_6_4_5_1_314
  48 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 229 (accept_3_3 47
  172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 229
  (Polychromatic418967fa.accept_11_2_7_9_1_890 46 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 172 229 (accept_3_3 44 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 172 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 172 229 (Polychromatic418967fa.accept_9_6_1_4_1_474
  42 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 229 (accept_3_3 41
  172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 229
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 172 229 (accept_3_3 38 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 172 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 172 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36
  172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 229 (accept_3_3 35
  172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 229 (accept_3_3 32 172 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 172 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 172 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 172 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 172 229 (accept_3_3 29 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 172 229 (Polychromatic418967fa.accept_17_11_2_8_1_7569 28 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 172 229 (accept_3_3 26 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 172 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 172 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 172 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 172 229 (accept_3_3 23 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 172 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 229 (accept_3_3 20 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 172 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 172 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 229
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 172 229 (accept_3_3 17 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 172 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 229 (accept_3_3 14 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 172 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 172 229 (accept_3_3 11 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 172 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 229 (accept_3_3 8 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 172 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 172 229 (accept_3_3 5 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  172 229 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 172 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 172 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 229 (accept_3_3 2 172 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 172 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 171 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 171 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 171 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 229 (accept_3_3 56 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 229 (Polychromatic418967fa.accept_10_5_1_9_1_791
  55 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 229 (accept_3_3 53 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 171 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 229 (accept_3_3 50 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 229
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 229 (accept_3_3 47 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 229 (accept_3_3 44 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 229 (accept_3_3 41 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 229 (accept_3_3 38 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 229 (accept_3_3 35 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 229 (accept_3_3 32 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 229 (Polychromatic418967fa.accept_25_6_21_4_1_13718 31 171
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 229 (accept_3_3 29 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 229 (Polychromatic418967fa.accept_21_6_3_19_1_10785 27 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 229 (accept_3_3 26 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 171
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 229
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 229 (accept_3_3 23 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 229 (accept_3_3 20 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 171
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 229 (accept_3_3 17 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 229 (accept_3_3 14 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 171 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 229
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 229 (accept_3_3 11 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 229 (accept_3_3 8 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 229 (accept_3_3 5 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 229 (accept_3_3 2 171 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 171 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 170 229 (Eq.refl Bool.true) (allA_of_3_1
  60 170 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 169 229 (Eq.refl Bool.true) (allA_succ_of_accept 60
  169 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 169 229 (accept_3_3 59 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 169 229 (Polychromatic418967fa.accept_17_7_16_8_1_7613 58 169 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 169 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 229 (accept_3_3 56 169 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 229 (Polychromatic418967fa.accept_7_6_1_5_1_322
  55 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 229
  (Polychromatic418967fa.accept_19_16_17_1_1_4011 54 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 169 229 (accept_3_3 53 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 169 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 169 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 169 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 229 (accept_3_3 50 169 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 229 (Polychromatic418967fa.accept_16_1_9_5_1_5443
  49 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 229 (accept_3_3 47 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 229 (accept_3_3 44 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 229 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 169 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 229 (accept_3_3 41 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 229 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 229 (accept_3_3 38 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 229 (accept_3_3 35 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 229 (accept_3_3 32 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 229 (accept_3_3 29 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 229 (accept_3_3 26 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 229 (accept_3_3 23 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 229 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 229 (accept_3_3 20 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 229 (accept_3_3 17 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 229 (Polychromatic418967fa.accept_19_16_17_1_1_4011 16 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 229 (accept_3_3 14 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 229 (accept_3_3 11 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 229 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 229 (accept_3_3 8 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 229 (Polychromatic418967fa.accept_17_7_16_8_1_7613 7 169
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 229 (accept_3_3 5 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 169 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 229 (accept_3_3 2 169 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 168 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 168 229 (Polychromatic418967fa.accept_16_12_8_5_1_3316 60 168
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 168 229 (accept_3_3 59 168
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 229
  (Polychromatic418967fa.accept_25_8_18_4_1_13697 58 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 168 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 229 (accept_3_3 56 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 168 229 (accept_3_3 53 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 168 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 229 (accept_3_3 50 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 168
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 168 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 168 229 (accept_3_3 47 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 168 229 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 229 (accept_3_3 44 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 168 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 229
  (Polychromatic418967fa.accept_19_4_16_1_1_8332 42 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 168 229 (accept_3_3 41 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 168 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 168 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 229 (accept_3_3 38 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 229
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 168 229 (accept_3_3 35 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 229 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 168
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 229 (accept_3_3 32 168
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 229
  (Polychromatic418967fa.accept_10_1_8_9_1_787 31 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 168 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 229 (accept_3_3 29 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 229 (Polychromatic418967fa.accept_10_7_8_9_1_785
  27 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 229 (accept_3_3 26
  168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 168 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 229 (accept_3_3 23 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 168 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 168 229 (accept_3_3 20 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 168 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 229 (accept_3_3 17 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 168 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 229
  (Polychromatic418967fa.accept_19_15_16_1_1_11087 15 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 229 (accept_3_3 14 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 229 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 168 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 168 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 229 (accept_3_3 11 168 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 229
  (Polychromatic418967fa.accept_13_9_12_8_1_570 9 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 168 229 (accept_3_3 8 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  168 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 168 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 229 (accept_3_3 5 168 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 168 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 229 (accept_3_3 2 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 167 229
  (Eq.refl Bool.true) (allA_of_3_1 63 167 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 166 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 166 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 166 229 (accept_3_3 62 166 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 166 229 (Polychromatic418967fa.accept_18_7_4_13_1_3315 61 166 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 166 229
  (Polychromatic418967fa.accept_23_14_5_22_1_13717 60 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 166 229 (accept_3_3 59 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 166 229 (Polychromatic418967fa.accept_26_6_10_21_1_13716 58 166 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 166 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57
  166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 166 229 (accept_3_3 56
  166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 166 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 166 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 166 229 (accept_3_3 53 166 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 166 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 166 229 (accept_3_3 50 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 166 229 (Polychromatic418967fa.accept_14_7_12_5_1_1861 49 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 166 229 (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 229 (accept_3_3 47 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 166 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 46 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 166 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 166 229 (accept_3_3 44 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 166 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 166 229 (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 229 (accept_3_3 41 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 166 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 229 (accept_3_3 38 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 229 (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 229 (accept_3_3 35 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 229 (Polychromatic418967fa.accept_19_15_14_1_1_8297 34 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 229 (accept_3_3 32 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 166 229 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 229 (accept_3_3 29 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 229 (accept_3_3 26 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 229 (accept_3_3 23 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 229 (Polychromatic418967fa.accept_17_5_13_8_1_7556 22 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 229 (accept_3_3 20 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 229 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 229 (accept_3_3 17 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 229 (accept_3_3 14 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 229 (accept_3_3 11 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 166
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 229 (accept_3_3 8 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 229 (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 229 (accept_3_3 5 166 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 166 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 229 (accept_3_3 2 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 229 (Polychromatic418967fa.accept_16_1_6_5_1_4385 1 166 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 165 229
  (Eq.refl Bool.true) (allA_succ_of_accept 64 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 165 229 (accept_3_3 62 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 165 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 165 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 229 (accept_3_3 59 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 165 229 (accept_3_3 56 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 165 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 165 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 229 (accept_3_3 53 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 165 229 (accept_3_3 50 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 165 229 (Polychromatic418967fa.accept_21_7_18_19_1_10715 49 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 229 (accept_3_3 47 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 165 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 229
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 45 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 165 229 (accept_3_3 44 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 165 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 165 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 229 (accept_3_3 41 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 229 (accept_3_3 38 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 165 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 229 (accept_3_3 35 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 229 (accept_3_3 32 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 229 (accept_3_3 29 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 229 (accept_3_3 26 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 229 (accept_3_3 23 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 229 (accept_3_3 20 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 229 (Polychromatic418967fa.accept_19_18_13_1_1_9735 18 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 229 (accept_3_3 17 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 229 (accept_3_3 14 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 229 (accept_3_3 11 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 165 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 229 (accept_3_3 8 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 229 (accept_3_3 5 165 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 229 (accept_3_3 2 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 165 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 164 229
  (Eq.refl Bool.true) (allA_of_3_1 66 164 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 163 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 229 (accept_3_3 65 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 229
  (Polychromatic418967fa.accept_14_7_9_5_1_529 63 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 229 (accept_3_3 62 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 229 (accept_3_3 59 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 229 (accept_3_3 56 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 229 (Polychromatic418967fa.accept_13_3_7_8_1_4192 55 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 229 (accept_3_3 53 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 229 (accept_3_3 50 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 229 (accept_3_3 47 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 229 (accept_3_3 44 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 229 (accept_3_3 41 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 229 (accept_3_3 38 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 229 (Polychromatic418967fa.accept_19_18_11_1_1_4035 37 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 229 (accept_3_3 35 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 229 (accept_3_3 32 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 229 (accept_3_3 29 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 229
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 229 (accept_3_3 26 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 229 (accept_3_3 23 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 229 (accept_3_3 20 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 229 (Polychromatic418967fa.accept_17_2_10_8_1_7691 19 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 229 (accept_3_3 17 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 229 (accept_3_3 14 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 229 (Polychromatic418967fa.accept_21_13_16_19_1_1828 13 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 229 (accept_3_3 11 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 229
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 229 (accept_3_3 8 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 229 (accept_3_3 5 163 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 163 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 229 (accept_3_3 2 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 163 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 162
  229 (Eq.refl Bool.true) (allA_succ_of_accept 67 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 162 229 (accept_3_3 65 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 162 229 (Polychromatic418967fa.accept_19_7_10_1_1_5382 64 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 229 (accept_3_3 62 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 162 229 (accept_3_3 59 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 162 229 (Polychromatic418967fa.accept_25_8_12_4_1_13715 58 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 162 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 229 (accept_3_3 56 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 162 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 54 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 229 (accept_3_3 53 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 162 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 229 (accept_3_3 50 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 229 (Polychromatic418967fa.accept_19_11_10_1_1_2773 49 162 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 229 (accept_3_3 47 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 229 (accept_3_3 44 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 229
  (Polychromatic418967fa.accept_19_4_10_1_1_2776 42 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 162 229 (accept_3_3 41 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 162 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 229 (accept_3_3 38 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 229 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 229
  (Polychromatic418967fa.accept_19_17_10_1_1_6795 36 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 229 (accept_3_3 35 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 162 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 229 (Polychromatic418967fa.accept_17_16_9_8_1_5063 33 162
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 229 (accept_3_3 32 162
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 162 229 (Polychromatic418967fa.accept_19_11_10_1_1_2773 30 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 229 (accept_3_3 29 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 162 229 (accept_3_3 26 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 162 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 162 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 229 (accept_3_3 23 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 22 162 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 229
  (Polychromatic418967fa.accept_10_1_2_9_1_152 21 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 162 229 (accept_3_3 20 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 162 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 229 (accept_3_3 17 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 162 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 162 229 (accept_3_3 14 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 162 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 162 229 (Polychromatic418967fa.accept_20_12_2_9_1_13714 12 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 229 (accept_3_3 11 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 162 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 162 229 (accept_3_3 8 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  162 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 162 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 229 (accept_3_3 5 162 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 162 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 162 229 (accept_3_3 2 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  162 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 162 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 162 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 161
  229 (Eq.refl Bool.true) (allA_of_3_1 69 161 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 160 229
  (Eq.refl Bool.true) (allA_succ_of_accept 69 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 160 229 (accept_3_3 68 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 160 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 160 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 160 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 160 229 (accept_3_3 65 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 160 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 229 (accept_3_3 62 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 160 229 (Polychromatic418967fa.accept_13_9_4_8_1_1752 61 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 160 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 160 229 (accept_3_3 59 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 160 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 160 229 (accept_3_3 56 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 160 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 160 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 160 229 (accept_3_3 53 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 160 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 160 229 (accept_3_3 50 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 160 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 160 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 160 229 (accept_3_3 47 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 160 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 229 (accept_3_3 44 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 229 (accept_3_3 41 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 229 (Polychromatic418967fa.accept_19_2_8_1_1_4065 40 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 229 (accept_3_3 38 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 229 (accept_3_3 35 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 229 (accept_3_3 32 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 229 (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 160 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 229 (accept_3_3 29 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 229 (accept_3_3 26 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 229 (accept_3_3 23 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 229 (accept_3_3 20 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 229 (accept_3_3 17 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 229 (Polychromatic418967fa.accept_17_16_7_8_1_7638 16 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 229 (accept_3_3 14 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 229 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 160 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 229 (accept_3_3 11 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 229 (accept_3_3 8 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 229 (accept_3_3 5 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 160 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 229 (accept_3_3 2 160 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 160 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 159 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 159 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 229 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 159
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 229 (accept_3_3 68 159
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 229
  (Polychromatic418967fa.accept_19_10_7_1_1_1685 67 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 159 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 229 (accept_3_3 65 159 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 229
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 159 229 (accept_3_3 62 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 159 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 159 229 (Polychromatic418967fa.accept_17_9_6_8_1_6315 60 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 229 (accept_3_3 59 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 159 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 159 229 (accept_3_3 56 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 159 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 229 (accept_3_3 53 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 229
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 229 (accept_3_3 50 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 159 229 (Polychromatic418967fa.accept_16_1_15_5_1_708 49 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 229 (accept_3_3 47 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 229 (accept_3_3 44 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 159 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 229 (accept_3_3 41 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 159 229 (accept_3_3 38 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 159 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 229 (accept_3_3 35 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 229 (accept_3_3 32 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 229 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 229 (accept_3_3 29 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 229 (accept_3_3 26 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 229 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 229 (accept_3_3 23 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 229 (accept_3_3 20 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 229 (accept_3_3 17 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 229
  (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 229 (accept_3_3 14 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 229 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 229 (accept_3_3 11 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 229 (accept_3_3 8 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 229 (accept_3_3 5 159 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 229 (accept_3_3 2 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 159 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72
  158 229 (Eq.refl Bool.true) (allA_of_3_1 72 158 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 157 229
  (Eq.refl Bool.true) (allA_succ_of_accept 72 157 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 229 (accept_3_3 71 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 157
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 229
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 69 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 229 (accept_3_3 68 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 229 (Polychromatic418967fa.accept_20_7_17_9_1_10825 67 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 229 (Polychromatic418967fa.accept_16_2_13_5_1_2257 66 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 229 (accept_3_3 65 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 157 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 229
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 229 (accept_3_3 62 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 61 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 229 (Polychromatic418967fa.accept_19_3_5_1_1_6811 60 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 229 (accept_3_3 59 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 157 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 229 (accept_3_3 56 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 229 (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 229 (accept_3_3 53 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 52 157
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 229 (accept_3_3 50 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 229 (Polychromatic418967fa.accept_16_1_13_5_1_2280 49 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 229 (accept_3_3 47 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 46 157
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 229
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 229 (accept_3_3 44 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 229 (accept_3_3 41 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 229 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 157
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 229
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 229 (accept_3_3 38 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 229 (accept_3_3 35 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 229 (Polychromatic418967fa.accept_16_2_13_5_1_2257 34 157 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 229
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 229 (accept_3_3 32 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 229 (accept_3_3 29 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 229
  (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 229 (accept_3_3 26 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 229 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 229 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 229 (accept_3_3 23 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 157 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 229
  (Polychromatic418967fa.accept_25_21_7_4_1_6458 21 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 229 (accept_3_3 20 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 229 (accept_3_3 17 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 157 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 229 (accept_3_3 14 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 229 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 229 (accept_3_3 11 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 157
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 229 (accept_3_3 8 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 229 (accept_3_3 5 157 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 229 (Polychromatic418967fa.accept_19_4_5_1_1_4077 4 157 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 229
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 229 (accept_3_3 2 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 157 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  156 229 (Eq.refl Bool.true) (allA_succ_of_accept 73 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 156 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 156 229
  (Polychromatic418967fa.accept_16_8_12_5_1_200 72 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 156 229 (accept_3_3 71 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 156 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 229 (accept_3_3 68 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 156 229 (accept_3_3 65 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 156 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 156 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 229 (accept_3_3 62 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 156 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 229 (accept_3_3 59 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 156 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 58 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 229 (accept_3_3 56 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 229
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 54 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 156 229 (accept_3_3 53 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 156 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 229 (accept_3_3 50 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 229
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 229 (accept_3_3 47 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 229 (accept_3_3 44 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 229 (accept_3_3 41 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 229 (accept_3_3 38 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 229
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 229 (accept_3_3 35 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 229 (accept_3_3 32 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 229
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 30 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 156 229 (accept_3_3 29 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 156 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 156 229 (Polychromatic418967fa.accept_20_7_16_9_1_4970 27 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 229 (accept_3_3 26 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 156 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 229 (accept_3_3 23 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 229 (Polychromatic418967fa.accept_17_5_3_8_1_1697 22 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 229 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 229 (accept_3_3 20 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 156 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 229 (accept_3_3 17 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 229 (accept_3_3 14 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 229
  (Polychromatic418967fa.accept_17_12_3_8_1_7627 12 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 229 (accept_3_3 11 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 229 (accept_3_3 8 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 229 (accept_3_3 5 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 156 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 229 (accept_3_3 2 156 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 156 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 155 229 (Eq.refl
  Bool.true) (allA_of_3_1 75 155 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 154 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 154 229 (accept_3_3 74 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 154 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 73 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 154 229 (Polychromatic418967fa.accept_17_4_1_8_1_5070
  72 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 229 (accept_3_3 71
  154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 154 229
  (Polychromatic418967fa.accept_9_7_1_4_1_217 70 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 154 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 229 (accept_3_3 68 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 154 229 (Polychromatic418967fa.accept_9_3_1_4_1_216
  66 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 229 (accept_3_3 65
  154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 229
  (Polychromatic418967fa.accept_12_4_10_1_1_706 64 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 154 229 (accept_3_3 62 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 154 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 229 (Polychromatic418967fa.accept_9_6_1_4_1_474
  60 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 229 (accept_3_3 59
  154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 154 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 154 229 (accept_3_3 56 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 229
  (Polychromatic418967fa.accept_21_12_7_19_1_10736 54 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 154 229 (accept_3_3 53 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 154 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 154 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 229 (accept_3_3 50 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 229
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 154 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 229 (accept_3_3 47 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 229 (Polychromatic418967fa.accept_16_14_10_5_1_1393 46 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 154 229 (accept_3_3 44 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 154 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 229 (accept_3_3 41 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 229 (accept_3_3 38 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 229 (Polychromatic418967fa.accept_18_1_10_13_1_500 37 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 229 (accept_3_3 35 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 229 (accept_3_3 32 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 229 (accept_3_3 29 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 229 (accept_3_3 26 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 229 (accept_3_3 23 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 229 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 229 (accept_3_3 20 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 229 (accept_3_3 17 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 229 (accept_3_3 14 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 229 (accept_3_3 11 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 154 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 229 (accept_3_3 8 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 229 (accept_3_3 5 154 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 154 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 229 (accept_3_3 2 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 229 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 154 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 153 229 (Eq.refl Bool.true) (allA_succ_of_accept 76 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 153 229 (accept_3_3 74 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 153 229 (Polychromatic418967fa.accept_24_1_9_13_1_13713 73 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 153 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 72 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 229 (accept_3_3 71 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 229
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 69 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 229 (accept_3_3 68 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 66 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 229 (accept_3_3 65 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 229
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 229 (accept_3_3 62 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 229 (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 229 (accept_3_3 59 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 229 (accept_3_3 56 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 229 (Polychromatic418967fa.accept_21_13_6_19_1_4489 55 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 229 (accept_3_3 53 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 229 (accept_3_3 50 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 229 (Polychromatic418967fa.accept_16_1_9_5_1_5443 49 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 229 (Polychromatic418967fa.accept_14_6_13_5_1_534 48 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 229 (accept_3_3 47 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 229
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 229 (accept_3_3 44 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 229 (Polychromatic418967fa.accept_18_6_9_13_1_3320 42 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 229 (accept_3_3 41 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 229 (accept_3_3 38 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 229 (accept_3_3 35 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 229
  (Polychromatic418967fa.accept_13_7_10_8_1_567 33 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 229 (accept_3_3 32 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 229 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 229 (accept_3_3 29 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 229 (accept_3_3 26 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 229 (accept_3_3 23 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 229
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 229 (accept_3_3 20 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 229 (accept_3_3 17 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 229 (accept_3_3 14 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 229 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 229 (accept_3_3 11 153 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 229
  (Polychromatic418967fa.accept_27_9_18_13_1_13712 9 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 229 (accept_3_3 8 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 153 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 229 (accept_3_3 5 153 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 229 (accept_3_3 2 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 153 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 152 229 (Eq.refl Bool.true) (allA_of_3_1 78 152 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 151 229
  (Eq.refl Bool.true) (allA_succ_of_accept 78 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 229 (accept_3_3 77 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 151 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 229 (accept_3_3 74 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 229 (accept_3_3 71 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 229 (accept_3_3 68 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 229 (Polychromatic418967fa.accept_24_19_7_13_1_10414 67 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 229 (accept_3_3 65 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 151 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 229
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 229 (accept_3_3 62 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 229 (Polychromatic418967fa.accept_17_10_15_8_1_6324 61 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 229 (accept_3_3 59 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 229 (accept_3_3 56 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 229 (accept_3_3 53 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 229 (accept_3_3 50 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 229 (Polychromatic418967fa.accept_19_11_18_1_1_4048 49 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 229 (accept_3_3 47 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 229 (accept_3_3 44 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 229 (accept_3_3 41 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 229 (Polychromatic418967fa.accept_17_6_15_8_1_1714 40 151 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 229 (accept_3_3 38 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 229 (accept_3_3 35 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 229 (accept_3_3 32 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 229 (Polychromatic418967fa.accept_19_12_18_1_1_12336 31 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 229 (accept_3_3 29 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 151 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 229 (accept_3_3 26 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 229 (accept_3_3 23 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 229 (accept_3_3 20 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 229 (accept_3_3 17 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 229 (accept_3_3 14 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 229 (accept_3_3 11 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 229 (accept_3_3 8 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 229 (Polychromatic418967fa.accept_19_7_18_1_1_1662 7 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 229 (accept_3_3 5 151 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 229 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 151 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 229 (accept_3_3 2 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 151 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 150 229 (Eq.refl Bool.true) (allA_succ_of_accept 79 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50
  79 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 150 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 150 229 (accept_3_3 77 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 150 229 (Polychromatic418967fa.accept_20_16_10_9_1_9431 76 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 150 229 (accept_3_3 74 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 150 229 (accept_3_3 71 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 150 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 150 229 (Polychromatic418967fa.accept_21_6_3_19_1_10785 69 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 229 (accept_3_3 68 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 150 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 150 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 150 229 (accept_3_3 65 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 150 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 229 (accept_3_3 62 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 150 229
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 150 229 (accept_3_3 59 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 150 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 150 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 229 (accept_3_3 56 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 229
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 150 229 (accept_3_3 53 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 150 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 229 (accept_3_3 50 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 150 229 (accept_3_3 47 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 150 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 150 229 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 229 (accept_3_3 44 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 150 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 229
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 42 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 150 229 (accept_3_3 41 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 150 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 229 (accept_3_3 38 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 229 (accept_3_3 35 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 229 (Polychromatic418967fa.accept_16_1_6_5_1_4385 33 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 229 (accept_3_3 32 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 229 (accept_3_3 29 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 229 (accept_3_3 26 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 229
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 229 (accept_3_3 23 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 229 (accept_3_3 20 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 229
  (Polychromatic418967fa.accept_19_18_17_1_1_2789 18 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 229 (accept_3_3 17 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 150 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 229 (accept_3_3 14 150 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 229 (Polychromatic418967fa.accept_11_2_7_9_1_890
  13 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 229 (accept_3_3 11 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 229 (accept_3_3 8 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 229
  (Polychromatic418967fa.accept_17_6_14_8_1_3858 6 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 229 (accept_3_3 5 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 229 (Polychromatic418967fa.accept_16_4_6_5_1_2245 4 150 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 229 (accept_3_3 2 150 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 150 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 149 229 (Eq.refl
  Bool.true) (allA_of_3_1 81 149 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 148 229 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 148 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 229 (accept_3_3 80 148 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 148 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 79 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 148 229
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 78 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 148 229 (accept_3_3 77 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 148 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 148 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 229 (accept_3_3 74 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 148 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73
  148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 229
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 72 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 148 229 (accept_3_3 71 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 148 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 229 (accept_3_3 68 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 148 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 229 (accept_3_3 65 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 229 (accept_3_3 62 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 61 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 229 (accept_3_3 59 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 229 (accept_3_3 56 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 229 (accept_3_3 53 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 229 (accept_3_3 50 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 229 (accept_3_3 47 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 229 (accept_3_3 44 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 229 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 229
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 229 (accept_3_3 41 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 229 (accept_3_3 38 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 229
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 229 (accept_3_3 35 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 229 (accept_3_3 32 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 229
  (Polychromatic418967fa.accept_19_11_15_1_1_12391 30 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 148 229 (accept_3_3 29 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 148 229 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 148 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 229 (accept_3_3 26 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 229 (Polychromatic418967fa.accept_7_4_1_5_1_540
  25 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 229 (accept_3_3 23 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 229 (accept_3_3 20 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 229 (Polychromatic418967fa.accept_20_19_8_9_1_4963 19 148 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 229 (accept_3_3 17 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 229 (accept_3_3 14 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 229
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 229 (accept_3_3 11 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 229 (accept_3_3 8 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 229 (accept_3_3 5 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 148 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 229 (accept_3_3 2 148 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 148 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 147 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 229 (Polychromatic418967fa.accept_12_9_3_1_1_303
  81 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 229 (accept_3_3 80
  147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 229
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 147 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 229 (accept_3_3 77 147 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 229
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 75 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 229 (accept_3_3 74 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 147 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 229 (accept_3_3 71 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 147 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 229 (accept_3_3 68 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 229 (Polychromatic418967fa.accept_15_7_12_4_1_1236 67 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 229 (accept_3_3 65 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 229
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 229 (accept_3_3 62 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 229 (accept_3_3 59 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 229
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 229 (accept_3_3 56 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 229 (accept_3_3 53 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 229 (accept_3_3 50 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 229 (accept_3_3 47 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 229 (accept_3_3 44 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 229 (accept_3_3 41 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 229
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 229 (accept_3_3 38 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 229 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 229 (accept_3_3 35 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 229 (accept_3_3 32 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 229 (accept_3_3 29 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 229
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 229 (accept_3_3 26 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 229 (accept_3_3 23 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 229 (accept_3_3 20 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 229 (accept_3_3 17 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 229 (accept_3_3 14 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 229 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 229 (accept_3_3 11 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 229 (accept_3_3 8 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 229 (accept_3_3 5 147 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 229
  (Polychromatic418967fa.accept_22_3_15_9_1_10617 3 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 229 (accept_3_3 2 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 147 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 146 229 (Eq.refl Bool.true) (allA_of_3_1 84 146 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 145 229 (Eq.refl Bool.true) (allA_succ_of_accept 84 145 229 (Polychromatic418967fa.accept_8_4_1_5_1_186
  84 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 229 (accept_3_3 83
  145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 229
  (Polychromatic418967fa.accept_15_7_10_4_1_151 82 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 145 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 145 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 229 (accept_3_3 80 145 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 229 (Polychromatic418967fa.accept_9_6_1_4_1_474
  78 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 229 (accept_3_3 77
  145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 76 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 145 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 145 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 229 (accept_3_3 74 145 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 145 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 73 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 229
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 229 (accept_3_3 71 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 229 (accept_3_3 68 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 67 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 229 (accept_3_3 65 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 229 (Polychromatic418967fa.accept_16_15_1_5_1_2265 63 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 229 (accept_3_3 62 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 229 (accept_3_3 59 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 58 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 229 (accept_3_3 56 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 229 (Polychromatic418967fa.accept_20_15_5_9_1_3479 55 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 229
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 229 (accept_3_3 53 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 229 (accept_3_3 50 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 229 (accept_3_3 47 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 46 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 229 (accept_3_3 44 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 229 (accept_3_3 41 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 229 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 229 (accept_3_3 38 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 229 (accept_3_3 35 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 229 (accept_3_3 32 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 229 (accept_3_3 29 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 229 (Polychromatic418967fa.accept_19_8_12_1_1_11084 27 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 229 (accept_3_3 26 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 229 (accept_3_3 23 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 229 (accept_3_3 20 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 229
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 229 (accept_3_3 17 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 229 (accept_3_3 14 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 229
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 229 (accept_3_3 11 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 229 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 229 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 229 (accept_3_3 8 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 229 (accept_3_3 5 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 145 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 229 (accept_3_3 2 145 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 145 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 144 229
  (Eq.refl Bool.true) (allA_succ_of_accept 85 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 144 229
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 144 229 (accept_3_3 83 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 144 229 (Polychromatic418967fa.accept_19_6_11_1_1_6815 82 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 144 229 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 229 (accept_3_3 80 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 144 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 144 229 (accept_3_3 77 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 144 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 229 (accept_3_3 74 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 144 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 73 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 144 229 (accept_3_3 71 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 144 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 229 (accept_3_3 68 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 229 (Polychromatic418967fa.accept_19_10_11_1_1_8318 67 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 229
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 66 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 144 229 (accept_3_3 65 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 229 (accept_3_3 62 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 229 (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 229
  (Polychromatic418967fa.accept_19_3_11_1_1_8319 60 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 144 229 (accept_3_3 59 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 229 (accept_3_3 56 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 229
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 144 229 (accept_3_3 53 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 144 229 (Polychromatic418967fa.accept_28_24_4_5_1_11753 52 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 229 (accept_3_3 50 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 229 (Polychromatic418967fa.accept_21_7_18_19_1_10715 49 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 144 229 (accept_3_3 47 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 144 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 46 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 229 (accept_3_3 44 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 229
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 42 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 229 (accept_3_3 41 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 144 229 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 229 (Polychromatic418967fa.accept_20_19_4_9_1_5025 39 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 229 (accept_3_3 38 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 144 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 229 (accept_3_3 35 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 229 (accept_3_3 32 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 229 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 144 229 (accept_3_3 29 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 144 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 229 (accept_3_3 26 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 229
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 229 (accept_3_3 23 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 229 (accept_3_3 20 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 229 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 144
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 229
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 144 229 (accept_3_3 17 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 229 (accept_3_3 14 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 229
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 144 229 (accept_3_3 11 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 144 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 144 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 229 (accept_3_3 8 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 229 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 144 229 (accept_3_3 5 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  144 229 (Polychromatic418967fa.accept_21_4_18_19_1_9189 4 144 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 144 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 229 (accept_3_3 2 144 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 144 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 143 229
  (Eq.refl Bool.true) (allA_of_3_1 87 143 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 142 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 142 229 (accept_3_3 86 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 142 229 (Polychromatic418967fa.accept_11_8_10_9_1_1401 85 142 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 142 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 142 229 (accept_3_3 83 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 142 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 142 229 (accept_3_3 80 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 142 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 142 229 (accept_3_3 77 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 142 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 142 229 (accept_3_3 74 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 142 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 142 229
  (Polychromatic418967fa.accept_13_7_12_8_1_199 72 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 142 229 (accept_3_3 71 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 142 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 70 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 229 (accept_3_3 68 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 229 (accept_3_3 65 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 229 (accept_3_3 62 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 229 (accept_3_3 59 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 229 (Polychromatic418967fa.accept_16_10_14_5_1_5496 58 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 229 (accept_3_3 56 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 229
  (Polychromatic418967fa.accept_23_8_4_22_1_8781 54 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 229 (accept_3_3 53 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 229 (accept_3_3 50 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 142 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 229 (accept_3_3 47 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 229 (accept_3_3 44 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 229 (accept_3_3 41 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 229 (accept_3_3 38 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 229
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 142 229 (accept_3_3 35 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 142 229 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 142 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 229 (accept_3_3 32 142 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 229 (accept_3_3 29 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 229 (accept_3_3 26 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 229 (accept_3_3 23 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 229 (accept_3_3 20 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 229 (accept_3_3 17 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 229 (accept_3_3 14 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 229 (Polychromatic418967fa.accept_20_13_2_9_1_4958 13 142 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 229 (accept_3_3 11 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 229 (accept_3_3 8 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 229 (accept_3_3 5 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 142 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 229 (accept_3_3 2 142 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 142 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 141 229
  (Eq.refl Bool.true) (allA_succ_of_accept 88 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 141 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 141 229 (accept_3_3 86 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 141 229 (Polychromatic418967fa.accept_10_5_1_9_1_791 85 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 141 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 229 (accept_3_3 83 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 141 229 (accept_3_3 80 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 141 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 141 229 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 229 (accept_3_3 77 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 141 229 (accept_3_3 74 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 141 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 141 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 229 (accept_3_3 71 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 141 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 141 229 (accept_3_3 68 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 141 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 141 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 229 (accept_3_3 65 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 141 229 (accept_3_3 62 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 141 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 141 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 229 (accept_3_3 59 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 229 (accept_3_3 56 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 141 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 54 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 229 (accept_3_3 53 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 229 (accept_3_3 50 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 141 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 229 (accept_3_3 47 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 229 (accept_3_3 44 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 229 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 229 (accept_3_3 41 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 229 (accept_3_3 38 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 229 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 229 (accept_3_3 35 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 229
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 229 (accept_3_3 32 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 229 (accept_3_3 29 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 229 (accept_3_3 26 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 229 (accept_3_3 23 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 229 (accept_3_3 20 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 229 (accept_3_3 17 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 229
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 229 (accept_3_3 14 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 229 (accept_3_3 11 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 229
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 229 (accept_3_3 8 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 229 (accept_3_3 5 141 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 229 (accept_3_3 2 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 141 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 90 140 229 (Eq.refl Bool.true) (allA_of_3_1 90 140 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 91 139 229 (Eq.refl Bool.true) (allA_succ_of_accept 90 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2
  90 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 229 (accept_3_3 89
  139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 88 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 139 229 (Polychromatic418967fa.accept_16_7_11_5_1_4402 87 139 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 139 229 (accept_3_3 86 139 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 139 229
  (Polychromatic418967fa.accept_20_4_19_9_1_7961 84 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 139 229 (accept_3_3 83 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 139 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 229 (accept_3_3 80 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 139 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 79 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 229 (accept_3_3 77 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 76 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 229 (Polychromatic418967fa.accept_19_18_6_1_1_12398 75 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 229 (accept_3_3 74 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 229 (Polychromatic418967fa.accept_16_9_11_5_1_2279 73 139
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 229
  (Polychromatic418967fa.accept_13_7_9_8_1_188 72 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 229 (accept_3_3 71 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 69 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 229 (accept_3_3 68 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 139 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 229 (accept_3_3 65 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 229 (accept_3_3 62 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 229 (Polychromatic418967fa.accept_23_15_1_22_1_13711 61
  139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 229 (accept_3_3 59 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 229 (accept_3_3 56 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 55 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 229 (accept_3_3 53 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 229 (Polychromatic418967fa.accept_19_14_6_1_1_4022 52 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 229 (accept_3_3 50 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 139
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 229
  (Polychromatic418967fa.accept_14_6_13_5_1_534 48 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 229 (accept_3_3 47 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 229 (Polychromatic418967fa.accept_19_7_6_1_1_796 45 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 229 (accept_3_3 44 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 139 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 229 (accept_3_3 41 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 229 (accept_3_3 38 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 139 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 229 (accept_3_3 35 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 229 (accept_3_3 32 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 229 (Polychromatic418967fa.accept_23_8_1_22_1_13710 31 139
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 229 (accept_3_3 29 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 229 (Polychromatic418967fa.accept_20_8_19_9_1_6417 28 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 229 (accept_3_3 26 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 139 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 229
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 229 (accept_3_3 23 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 229 (Polychromatic418967fa.accept_19_2_6_1_1_9729 21 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 229 (accept_3_3 20 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 229 (Polychromatic418967fa.accept_25_19_14_4_1_13709 19
  139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 229 (accept_3_3 17 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 229 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 229 (accept_3_3 14 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 229 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 229
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 229 (accept_3_3 11 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 229 (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 229 (accept_3_3 8 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 139 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 229 (accept_3_3 5 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 139 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 229 (accept_3_3 2 139 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 138 229
  (Eq.refl Bool.true) (allA_succ_of_accept 91 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 138 229
  (Polychromatic418967fa.accept_21_6_12_19_1_6032 90 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 138 229 (accept_3_3 89 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 138 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 138 229 (accept_3_3 86 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 138 229 (Polychromatic418967fa.accept_19_9_5_1_1_2766
  85 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 138 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 84 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 138 229 (accept_3_3 83 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 138 229 (Polychromatic418967fa.accept_10_1_8_9_1_787 81 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 229 (accept_3_3 80 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 138 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 138 229 (accept_3_3 77 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 138 229 (Polychromatic418967fa.accept_15_1_3_4_1_1217 76 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 229 (accept_3_3 74 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 229
  (Polychromatic418967fa.accept_19_15_5_1_1_5360 72 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 138 229 (accept_3_3 71 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 229 (accept_3_3 68 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 229
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 66 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 229 (accept_3_3 65 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 138 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 229 (accept_3_3 62 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218
  61 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 229 (accept_3_3 59 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 229 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 229 (accept_3_3 56 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 229
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 229 (accept_3_3 53 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 229 (accept_3_3 50 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 229 (Polychromatic418967fa.accept_14_7_12_5_1_1861 49 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 229
  (Polychromatic418967fa.accept_21_6_12_19_1_6032 48 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 229 (accept_3_3 47 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 138 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 229 (Polychromatic418967fa.accept_14_3_12_5_1_153 45 138
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 229 (accept_3_3 44 138
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 138 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 138 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 229 (accept_3_3 41 138 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 138 229 (Polychromatic418967fa.accept_25_15_13_4_1_2948 40 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 138 229 (accept_3_3 38 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 138 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 229 (accept_3_3 35 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 138 229 (accept_3_3 32 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 138 229 (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 229 (accept_3_3 29 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 138 229 (accept_3_3 26 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 138 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 229 (accept_3_3 23 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 229 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 229
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 229 (accept_3_3 20 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 229 (Polychromatic418967fa.accept_19_18_5_1_1_8255 18 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 229 (accept_3_3 17 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 229 (accept_3_3 14 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 229 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 229 (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 229 (accept_3_3 11 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 138 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 229
  (Polychromatic418967fa.accept_19_9_5_1_1_2766 9 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 229 (accept_3_3 8 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 229 (accept_3_3 5 138 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 229 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 138 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 229 (accept_3_3 2 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 138 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 137 229
  (Eq.refl Bool.true) (allA_of_3_1 93 137 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 136 229 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 136 229 (accept_3_3 92 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 136 229 (Polychromatic418967fa.accept_16_11_8_5_1_4366 91 136 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 136 229
  (Polychromatic418967fa.accept_11_2_4_9_1_484 90 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 136 229 (accept_3_3 89 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 88 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 136 229 (accept_3_3 86 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 136 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 136 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 136 229 (accept_3_3 83 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 136 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 136 229 (accept_3_3 80 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 136 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 136 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 136 229 (accept_3_3 77 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 136 229 (Polychromatic418967fa.accept_13_11_6_8_1_1121 76 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 136 229 (accept_3_3 74 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 136 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 73 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 136 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 136 229 (accept_3_3 71 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 229 (accept_3_3 68 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 67 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 229 (accept_3_3 65 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 229 (accept_3_3 62 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 229 (accept_3_3 59 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 229 (accept_3_3 56 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 55 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 229
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 229 (accept_3_3 53 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 229 (accept_3_3 50 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 229 (Polychromatic418967fa.accept_19_11_3_1_1_2799 49 136 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 229 (accept_3_3 47 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 229 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 229 (accept_3_3 44 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 229 (accept_3_3 41 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 229 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 229 (accept_3_3 38 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 229 (accept_3_3 35 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 229 (accept_3_3 32 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 229 (Polychromatic418967fa.accept_24_7_16_13_1_13708 31 136 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 229 (accept_3_3 29 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 229 (accept_3_3 26 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 229 (accept_3_3 23 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 229 (accept_3_3 20 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 229 (Polychromatic418967fa.accept_16_3_8_5_1_6790 19 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 229
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 229 (accept_3_3 17 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 229 (accept_3_3 14 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 229 (accept_3_3 11 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 229 (accept_3_3 8 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 229 (accept_3_3 5 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 229 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 136 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 229 (accept_3_3 2 136 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 136 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 135
  229 (Eq.refl Bool.true) (allA_succ_of_accept 94 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 93 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 229 (accept_3_3 92 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 135 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 91 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 229 (accept_3_3 89 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 87 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 135 229 (accept_3_3 86 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 135 229 (Polychromatic418967fa.accept_19_9_2_1_1_2821 85 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 135 229 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 229 (accept_3_3 83 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 135 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 81 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 135 229 (accept_3_3 80 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 135 229 (Polychromatic418967fa.accept_13_1_5_8_1_207 79 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 229 (accept_3_3 77 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 229
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 75 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 229 (accept_3_3 74 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 229 (accept_3_3 71 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 135 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 229 (accept_3_3 68 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 229 (accept_3_3 65 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 229
  (Polychromatic418967fa.accept_14_7_9_5_1_529 63 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 135 229 (accept_3_3 62 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 135 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 135 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 229 (accept_3_3 59 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 229 (accept_3_3 56 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 229 (Polychromatic418967fa.accept_13_3_5_8_1_1099 55 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 229 (accept_3_3 53 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 135 229 (accept_3_3 50 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 135 229 (Polychromatic418967fa.accept_13_10_5_8_1_2555 49 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 229 (Polychromatic418967fa.accept_17_14_16_8_1_3861 48 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 229 (accept_3_3 47 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 229 (accept_3_3 44 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 229 (Polychromatic418967fa.accept_16_11_7_5_1_4364 43 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 229 (accept_3_3 41 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 229
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 229 (accept_3_3 38 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 229 (Polychromatic418967fa.accept_19_18_2_1_1_5375 37 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 229 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 229 (accept_3_3 35 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 229 (accept_3_3 32 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 229 (accept_3_3 29 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 229
  (Polychromatic418967fa.accept_13_1_5_8_1_207 27 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 229 (accept_3_3 26 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 229 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 229 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 229 (accept_3_3 23 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 229
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 229 (accept_3_3 20 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 229 (Polychromatic418967fa.accept_17_2_16_8_1_3881 19 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 229 (accept_3_3 17 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 229
  (Polychromatic418967fa.accept_19_15_2_1_1_2822 15 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 229 (accept_3_3 14 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 229 (Polychromatic418967fa.accept_19_13_2_1_1_4054 13 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 229 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 229 (accept_3_3 11 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 229 (accept_3_3 8 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 229 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 229 (accept_3_3 5 135 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 229
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 229 (accept_3_3 2 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 229 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 135 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 134
  229 (Eq.refl Bool.true) (allA_of_3_1 96 134 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 133 229
  (Eq.refl Bool.true) (allA_succ_of_accept 96 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 229 (accept_3_3 95 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 94 133
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 93 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 229 (accept_3_3 92 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 229 (Polychromatic418967fa.accept_20_10_13_9_1_6429 90 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 229 (accept_3_3 89 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 229 (Polychromatic418967fa.accept_21_4_7_19_1_13687 88 133
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 229 (accept_3_3 86 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 85 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 229 (accept_3_3 83 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 229
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 81 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 229 (accept_3_3 80 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 229 (Polychromatic418967fa.accept_14_9_7_5_1_1105 79 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 229 (accept_3_3 77 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 76 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 229 (accept_3_3 74 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 229 (accept_3_3 71 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 229 (Polychromatic418967fa.accept_13_5_3_8_1_1117 70 133
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 229 (accept_3_3 68 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 229 (Polychromatic418967fa.accept_17_16_14_8_1_7608 67 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 229 (accept_3_3 65 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 229
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 229 (accept_3_3 62 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 61 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 229 (accept_3_3 59 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 229 (Polychromatic418967fa.accept_14_2_7_5_1_5450 58 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 229 (accept_3_3 56 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 229 (accept_3_3 53 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 229 (Polychromatic418967fa.accept_21_10_7_19_1_9208 52 133
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 229 (accept_3_3 50 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 229 (Polychromatic418967fa.accept_22_5_1_9_1_5652 49 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 229 (accept_3_3 47 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 229
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 133 229 (accept_3_3 44 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 133 229 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 133 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 133 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 229 (accept_3_3 41 133 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 229
  (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 133 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 229 (accept_3_3 38 133 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 229 (accept_3_3 35
  133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 229
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 133 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 229 (accept_3_3 32 133 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 133 229 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 229 (accept_3_3 29 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 229 (Polychromatic418967fa.accept_22_5_1_9_1_5652 27 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 229 (accept_3_3 26 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 229 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 133
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 229 (accept_3_3 23 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 229 (accept_3_3 20 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 229
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 229 (accept_3_3 17 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 229 (accept_3_3 14 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 229 (Polychromatic418967fa.accept_21_13_7_19_1_4505 13 133 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 229
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 229 (accept_3_3 11 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 229 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 229 (accept_3_3 8 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 229 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 229
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 229 (accept_3_3 5 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 133 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 229 (accept_3_3 2 133 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  132 229 (Eq.refl Bool.true) (allA_succ_of_accept 97 132 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 97 132 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 132 229
  (Polychromatic418967fa.accept_21_12_6_19_1_1871 96 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 132 229 (accept_3_3 95 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 132 229 (Polychromatic418967fa.accept_26_16_2_21_1_6079 94 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210
  93 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 132 229 (accept_3_3 92
  132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 132 229
  (Polychromatic418967fa.accept_9_1_6_4_1_49 91 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 132 229 (Polychromatic418967fa.accept_17_5_13_8_1_7556 90 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 132 229 (accept_3_3 89 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 229 (Polychromatic418967fa.accept_10_7_2_9_1_775
  87 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 229 (accept_3_3 86
  132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 85 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 229 (accept_3_3 83 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141
  81 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 229 (accept_3_3 80
  132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 229
  (Polychromatic418967fa.accept_9_7_6_4_1_483 79 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 229 (accept_3_3 77 132 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 132 229 (Polychromatic418967fa.accept_15_1_12_4_1_2022 76 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 132 229 (accept_3_3 74 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 132 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 132 229 (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 229 (accept_3_3 71 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 132 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 229
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 69 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 132 229 (accept_3_3 68 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 229 (accept_3_3 65 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 229
  (Polychromatic418967fa.accept_16_15_4_5_1_1411 63 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 132 229 (accept_3_3 62 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 229 (accept_3_3 59 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 58 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 132 229 (accept_3_3 56 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 132 229 (Polychromatic418967fa.accept_15_9_12_4_1_2023 54 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 229 (accept_3_3 53 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 132 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 229
  (Polychromatic418967fa.accept_10_1_2_9_1_152 51 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 132 229 (accept_3_3 50 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 132 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 229 (accept_3_3 47 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 229
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 132 229 (accept_3_3 44 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 132 229 (Polychromatic418967fa.accept_20_2_12_9_1_6435 42 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 229 (accept_3_3 41 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 229 (Polychromatic418967fa.accept_16_8_4_5_1_4379 40 132
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 229
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 132 229 (accept_3_3 38 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 229 (accept_3_3 35 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 132 229 (accept_3_3 32 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 132 229 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 229 (accept_3_3 29 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 229
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 132 229 (accept_3_3 26 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 132 229 (Polychromatic418967fa.accept_15_9_12_4_1_2023 24 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 229 (accept_3_3 23 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 132 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 229 (accept_3_3 20 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 229 (accept_3_3 17 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 229
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 132 229 (accept_3_3 14 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 132 229 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 132 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 229 (accept_3_3 11 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 229
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 132 229 (accept_3_3 8 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  132 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 132 229 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 229 (accept_3_3 5 132 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 229 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 132 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 132 229 (accept_3_3 2 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  132 229 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 132 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  131 229 (Eq.refl Bool.true) (allA_of_3_1 99 131 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 130 229
  (Eq.refl Bool.true) (allA_succ_of_accept 99 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 130 229 (accept_3_3 98 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 130 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 130 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 130 229
  (Polychromatic418967fa.accept_15_6_10_4_1_150 96 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 130 229 (accept_3_3 95 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 130 229 (Polychromatic418967fa.accept_17_9_11_8_1_5077 94 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 130 229 (accept_3_3 92 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 130 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 90 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 130 229 (accept_3_3 89 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 130 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 130 229 (accept_3_3 86 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 130 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 130 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 84 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 130 229 (accept_3_3 83 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 130 229 (Polychromatic418967fa.accept_15_7_10_4_1_151 82 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 130 229 (accept_3_3 80 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 130 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 130 229 (accept_3_3 77 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 130 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 130 229 (accept_3_3 74 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 229 (Polychromatic418967fa.accept_15_13_10_4_1_1232 73 130 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 130 229 (accept_3_3 71 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 130 229 (Polychromatic418967fa.accept_17_2_11_8_1_2726 70 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 229 (accept_3_3 68 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 229
  (Polychromatic418967fa.accept_15_6_10_4_1_150 66 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 130 229 (accept_3_3 65 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 130 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 229 (accept_3_3 62 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 130 229 (Polychromatic418967fa.accept_16_13_2_5_1_3336 61 130 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 130 229
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 130 229 (accept_3_3 59 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 130 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 229 (accept_3_3 56 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 130 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 229 (accept_3_3 53 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 130 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 130 229 (accept_3_3 50 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 130 229 (Polychromatic418967fa.accept_21_7_4_19_1_4525 49 130 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 229 (accept_3_3 47 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 229 (Polychromatic418967fa.accept_18_10_4_13_1_3296 46 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 229 (accept_3_3 44 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 229
  (Polychromatic418967fa.accept_19_4_16_1_1_8332 42 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 229 (accept_3_3 41 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 229 (accept_3_3 38 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 130 229 (accept_3_3 35 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 130 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 229 (accept_3_3 32 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 229 (accept_3_3 29 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 229 (accept_3_3 26 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 229 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 130 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 229
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 24 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 229 (accept_3_3 23 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 229 (accept_3_3 20 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 229
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 229 (accept_3_3 17 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 229 (accept_3_3 14 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 229
  (Polychromatic418967fa.accept_21_12_4_19_1_4526 12 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 130 229 (accept_3_3 11 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 130 229 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 229 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 229 (accept_3_3 8 130
  229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50
  7 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 229 (accept_3_3 5 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 229 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 229 (accept_3_3 2 130 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 130 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 129 229 (Eq.refl Bool.true) (allA_succ_of_accept 100 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 129
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 99 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 129 229 (accept_3_3 98 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 129 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 129 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 96 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 229 (accept_3_3 95 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 93 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 129 229 (accept_3_3 92 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 129 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 129 229 (Polychromatic418967fa.accept_19_14_15_1_1_6806 90 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 229 (accept_3_3 89 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 229 (accept_3_3 86 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 229 (accept_3_3 83 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 229
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 229 (accept_3_3 80 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 79 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 229 (accept_3_3 77 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 229 (accept_3_3 74 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 229 (accept_3_3 71 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 229 (accept_3_3 68 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 229 (Polychromatic418967fa.accept_23_21_14_22_1_13707 67 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 229 (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 229 (accept_3_3 65 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64
  129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 229 (accept_3_3 62 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 229 (accept_3_3 59 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 229 (accept_3_3 56 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 229 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 229 (accept_3_3 53 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 229 (accept_3_3 50 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 229 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 229 (Polychromatic418967fa.accept_13_9_12_8_1_570 48 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 229 (accept_3_3 47 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 229
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 229 (accept_3_3 44 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 229 (accept_3_3 41 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 229 (accept_3_3 38 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 229 (accept_3_3 35 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 229
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 229 (accept_3_3 32 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 229 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 229 (accept_3_3 29 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 229 (accept_3_3 26 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 229 (accept_3_3 23 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 229
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 229 (accept_3_3 20 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 229 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 229 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 229 (accept_3_3 17 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 229
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 229 (accept_3_3 14 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 229 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 229 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 229 (accept_3_3 11 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 229
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 229 (accept_3_3 8 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 229 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 229 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 229 (accept_3_3 5 129 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 229
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 229 (accept_3_3 2 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 229 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 129 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 128 229 (Eq.refl Bool.true) (allA_of_3_1 102 128 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 127
  229 (Eq.refl Bool.true) (allA_succ_of_accept 102 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 229 (accept_3_3 101 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 229
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 100 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 127 229 (Polychromatic418967fa.accept_21_15_1_19_1_9205 99 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 229 (accept_3_3 98 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 97 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 229
  (Polychromatic418967fa.accept_9_6_1_4_1_474 96 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 229 (accept_3_3 95 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 93 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 229 (accept_3_3 92 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 229 (Polychromatic418967fa.accept_11_3_6_9_1_1378 91 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 127 229 (accept_3_3 89 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 88 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 229 (accept_3_3 86 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 229 (Polychromatic418967fa.accept_13_7_10_8_1_567 85 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 229 (accept_3_3 83 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 229 (accept_3_3 80 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 229 (accept_3_3 77 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 229 (accept_3_3 74 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 229
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 229 (accept_3_3 71 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 229 (accept_3_3 68 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 229 (accept_3_3 65 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 229 (Polychromatic418967fa.accept_13_12_10_8_1_3343 64 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 229 (accept_3_3 62 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 229
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 229 (accept_3_3 59 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 229 (accept_3_3 56 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 229 (accept_3_3 53 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 229 (accept_3_3 50 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 229 (Polychromatic418967fa.accept_16_1_15_5_1_708 49 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 229
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 229 (accept_3_3 47 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 229 (accept_3_3 44 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 229 (accept_3_3 41 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 229 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 229 (accept_3_3 38 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 229 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 229
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 229 (accept_3_3 35 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 229 (accept_3_3 32 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 229 (accept_3_3 29 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 229 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 229 (accept_3_3 26 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 229
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 229 (accept_3_3 23 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 229 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 229 (accept_3_3 20 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 229 (Polychromatic418967fa.accept_24_19_7_13_1_10414 19 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 229 (accept_3_3 17 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 229 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 229 (accept_3_3 14 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 229 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 229
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 229 (accept_3_3 11 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 229 (Polychromatic418967fa.accept_23_9_12_22_1_13706 9 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 229 (accept_3_3 8 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 229 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 229
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 229 (accept_3_3 5 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 229 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 127 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 229 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 229 (accept_3_3 2 127 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 229 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 127 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 126 229 (Eq.refl Bool.true) (allA_succ_of_accept 103 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 126 229
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 102 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 126 229 (accept_3_3 101 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 126 229 (Polychromatic418967fa.accept_15_10_6_4_1_1256 100 126 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 99
  126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 126 229 (accept_3_3 98
  126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 229
  (Polychromatic418967fa.accept_19_2_12_1_1_2815 97 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 126 229 (Polychromatic418967fa.accept_22_8_16_9_1_13705 96 126 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 229 (accept_3_3 95 126 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 94 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 229
  (Polychromatic418967fa.accept_10_3_6_9_1_779 93 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 126 229 (accept_3_3 92 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 126 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 90 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 229 (accept_3_3 89 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 88 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 126 229 (accept_3_3 86 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 126 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 85 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 126 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 84 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 126 229 (accept_3_3 83 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 82 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 229
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 81 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 126 229 (accept_3_3 80 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 126 229 (Polychromatic418967fa.accept_19_2_12_1_1_2815 78 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 126 229 (accept_3_3 77 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 76 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 126 229 (accept_3_3 74 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 126 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 73 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 126 229 (Polychromatic418967fa.accept_13_7_9_8_1_188 72 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 229 (accept_3_3 71 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 229 (Polychromatic418967fa.accept_15_10_6_4_1_1256 70 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 229
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 69 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 126 229 (accept_3_3 68 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 126 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 66 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 229 (accept_3_3 65 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 64 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 126 229 (accept_3_3 62 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 126 229 (Polychromatic418967fa.accept_19_4_12_1_1_3991 61 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 126 229 (Polychromatic418967fa.accept_23_14_11_22_1_13704 60 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 229 (accept_3_3 59 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 58 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 229
  (Polychromatic418967fa.accept_16_9_14_5_1_2239 57 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 126 229 (accept_3_3 56 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 126 229 (Polychromatic418967fa.accept_15_9_6_4_1_1220 54 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 229 (accept_3_3 53 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 229 (Polychromatic418967fa.accept_17_1_7_8_1_6347 52 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 126 229 (accept_3_3 50 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 126 229 (Polychromatic418967fa.accept_19_11_12_1_1_11049 49 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 229 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 126 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 229 (accept_3_3 47 126 229
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 229 (Polychromatic418967fa.accept_13_7_9_8_1_188
  46 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 229
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 229 (accept_3_3 44 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 126 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 42 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 229 (accept_3_3 41 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 229 (accept_3_3 38 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 126 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 229 (Polychromatic418967fa.accept_24_12_6_13_1_13703 36 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 229 (accept_3_3 35 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 229 (Polychromatic418967fa.accept_20_14_6_9_1_9460 34 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 229
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 126 229 (accept_3_3 32 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 126 229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 229 (accept_3_3 29 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 229 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 229 (accept_3_3 26 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 126 229 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 229 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 229 (accept_3_3 23 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 229 (Polychromatic418967fa.accept_24_22_6_13_1_13702 22
  126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 229
  (Polychromatic418967fa.accept_17_4_7_8_1_7491 21 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 126 229 (accept_3_3 20 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 126 229 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 229 (accept_3_3 17 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 229 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 229 (accept_3_3 14 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 126 229 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 229 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 229 (accept_3_3 11 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 229 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 126
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 229
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 229 (accept_3_3 8 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  126 229 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 126 229 (Polychromatic418967fa.accept_22_6_16_9_1_12093 6 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 229 (accept_3_3 5 126 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 229 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 126 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 229
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 126 229 (accept_3_3 2 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  126 229 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 126 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 125 229 (Eq.refl Bool.true) (allA_of_3_1 105 125 229 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 124 229 (Eq.refl Bool.true) (allA_succ_of_accept 105 124 229 (Polychromatic418967fa.accept_6_3_4_1_1_8
  105 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 124 229 (accept_3_3
  104 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 124 229
  (Polychromatic418967fa.accept_10_3_4_9_1_15 103 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 102 124 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 124 229 (accept_3_3 101 124 229 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 100 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 124 229 (accept_3_3 98 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 124 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 97 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 124 229 (accept_3_3 95 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 124 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 94 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 124 229 (accept_3_3 92 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 124 229 (Polychromatic418967fa.accept_13_12_7_8_1_1104 90 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 229 (accept_3_3 89 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 124 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 124
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 124 229 (accept_3_3 86 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 124 229 (Polychromatic418967fa.accept_10_5_4_9_1_420 85 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 229 (accept_3_3 83 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 124 229 (accept_3_3 80 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 124 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 79 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 78 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 229 (accept_3_3 77 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 124 229 (Polychromatic418967fa.accept_27_22_16_13_1_13701 76 124 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 124 229 (accept_3_3 74 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 124 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 124 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 229 (accept_3_3 71 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 124
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 229 (accept_3_3 68 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 67 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 229 (accept_3_3 65 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 124 229 (accept_3_3 62 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 124 229 (Polychromatic418967fa.accept_11_6_3_9_1_906 61 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 229 (accept_3_3 59 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 229 (accept_3_3 56 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 229 (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 229 (accept_3_3 53 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 229 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 124
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 229 (accept_3_3 50 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 229 (accept_3_3 47 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 229 (accept_3_3 44 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 229 (accept_3_3 41 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 229 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 229 (accept_3_3 38 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 229 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 229 (accept_3_3 35 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 124
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 229 (accept_3_3 32 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 229 (Polychromatic418967fa.accept_14_3_12_5_1_153 31 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 229 (accept_3_3 29 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 229 (accept_3_3 26 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 229 (accept_3_3 23 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 229 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 124 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 229 (accept_3_3 20 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 229 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 229 (accept_3_3 17 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 229 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 124
  229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 229 (accept_3_3 14 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 229 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 229 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 229 (accept_3_3 11 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 229 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 229 (accept_3_3 8 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 229 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 229 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 229 (accept_3_3 5 124 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 229 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 124 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 229
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 229 (accept_3_3 2 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 229 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 124 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  229))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 123 229 (Eq.refl Bool.true) (allA_succ_of_accept 106 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2
  106 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 105 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 123 229 (accept_3_3 104 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 123 229 (Polychromatic418967fa.accept_11_4_2_9_1_496 103 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 229 (accept_3_3 101 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 123 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 99 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 123 229 (accept_3_3 98 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 123 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 97 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 123 229 (Polychromatic418967fa.accept_10_6_3_9_1_1207 96 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 229 (accept_3_3 95 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 123 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 93 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 123 229 (accept_3_3 92 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 123 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 229 (accept_3_3 89 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 229
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 87 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 123 229 (accept_3_3 86 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 123 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 85 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 123 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 229 (accept_3_3 83 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 229
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 123 229 (accept_3_3 80 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 123 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 229 (accept_3_3 77 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 123 229 (accept_3_3 74 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 123 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 123 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 229 (accept_3_3 71 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 123 229 (accept_3_3 68 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 123 229 (Polychromatic418967fa.accept_13_2_6_8_1_1092 67 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 229 (accept_3_3 65 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 229
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 123 229 (accept_3_3 62 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 123 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 123 229 (Polychromatic418967fa.accept_22_16_13_9_1_13700 60 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 229 (accept_3_3 59 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 123 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 123 229 (accept_3_3 56 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 123 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 229 (accept_3_3 53 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 123 229 (accept_3_3 50 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 123 229 (Polychromatic418967fa.accept_19_11_9_1_1_2809 49 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 229 (accept_3_3 47 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 123 229 (accept_3_3 44 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 123 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 229 (accept_3_3 41 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 229 (accept_3_3 38 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 123 229 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 229 (accept_3_3 35 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 229
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 229 (accept_3_3 32 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 229 (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 229 (accept_3_3 29 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 229
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 229 (accept_3_3 26 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 229 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 229 (accept_3_3 23 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 229
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 229 (accept_3_3 20 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 229 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 229 (accept_3_3 17 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 229
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 229 (accept_3_3 14 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 229 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 229 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 229 (accept_3_3 11 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 229
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 229 (accept_3_3 8 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 229 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 229 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 229 (accept_3_3 5 123 229 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 229 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 229 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 229
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 229 (accept_3_3 2 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 229 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 123 229 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123
  229)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_229_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


