-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch231
-- name    : Polychromatic418967fa_Branch231
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:26:48.968775+00:00
-- url     : https://prove2.me/theorems/763d7317-5fea-4050-8b2a-a6028d728a0a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch231_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_231 : allB 231 231 :=
  allB_succ' 2 230 231 (Eq.refl Bool.true) (allA_succ_of_accept 1 230 231 (accept_3_4 1 230 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 231)) (allB_succ' 3 229 231 (Eq.refl Bool.true) (allA_succ_of_accept 2 229 231
  (accept_3_5 2 229 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 231
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 229 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 229 231))) (allB_succ' 4 228 231 (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 231 3 1 76 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 228 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 228 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 228 231)))) (allB_succ' 5 227 231 (Eq.refl Bool.true) (allA_succ_of_accept 4
  227 231 (accept_3_4 4 227 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 231
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 227 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 227 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 227 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 231 (accept_3_4 1 227 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 227 231))))) (allB_succ' 6 226 231 (Eq.refl Bool.true) (allA_succ_of_accept 5 226 231
  (accept_3_5 5 226 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 226 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 226 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 226 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 231 (accept_3_5 2 226 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 226 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 231)))))) (allB_succ' 7 225 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 225 231 3 2 75 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 225 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 225 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 225 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 231 3 1 75 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 225 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 231))))))) (allB_succ' 8 224 231 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  224 231 7 1 32 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 224 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 224 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 231 (accept_3_4 4 224 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 224 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 224 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 231 (accept_3_4 1 224 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  231)))))))) (allB_succ' 9 223 231 (Eq.refl Bool.true) (allA_succ_of_accept 8 223 231 (accept_3_5 8 223 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 231 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 223 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 231
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 223 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 231 (accept_3_5 5 223 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 223 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 231 (accept_3_5 2 223 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 223 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 231))))))))) (allB_succ' 10 222 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 222 231 3 3 74 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 222 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 222 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327
  7 222 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 231 3 2 74 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 222 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 231 3 1 74 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 222 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 231)))))))))) (allB_succ' 11 221 231 (Eq.refl Bool.true) (allA_succ_of_accept 10 221 231 (accept_3_4 10
  221 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 231
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 221 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 221 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 231 (accept_3_4 7 221 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 221 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 231 (Polychromatic418967fa.accept_15_5_11_6_1_692
  5 221 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 231 (accept_3_4 4
  221 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 221 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 221 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 231 (accept_3_4 1 221 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 221 231))))))))))) (allB_succ' 12 220 231 (Eq.refl Bool.true) (allA_succ_of_gcd 11 220 231 11 1
  20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 220 231
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 220 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 220 231 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 220 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 231 (accept_3_5 8 220 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 220 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 220 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  220 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 231 (accept_3_5 5 220
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 231
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 220 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 220 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 220 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 231 (accept_3_5 2 220 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 220 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 220 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 231)))))))))))) (allB_succ' 13 219 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 219 231 3 4 73 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 219 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 219 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 219 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 231 3 3 73 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 219 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 219 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 231 3 2 73 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 219 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 219 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 231 3 1 73 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 219 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 219 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 231))))))))))))) (allB_succ' 14 218 231
  (Eq.refl Bool.true) (allA_succ_of_accept 13 218 231 (accept_3_4 13 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 218 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 218 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 218 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 231 (accept_3_4 10 218 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  218 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 231 (accept_3_4 7 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 231 (accept_3_4 4 218 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 218 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 231
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 231 (accept_3_4 1 218 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  231)))))))))))))) (allB_succ' 15 217 231 (Eq.refl Bool.true) (allA_succ_of_gcd 14 217 231 7 2 31 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 217 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 217 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 217 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 217 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 231 (accept_3_5 11 217 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 217 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  217 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 231 (accept_3_5 8 217
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 217 231 7 1 31 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 217 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 231 (accept_3_5 5 217 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 217 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 217 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 231 (accept_3_5 2 217 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 217 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 231))))))))))))))) (allB_succ' 16 216 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 216 231 3 5 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 216 231 (Polychromatic418967fa.accept_19_14_7_3_1_5491 14 216 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 231
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 216 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 231 3 4 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 216 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 231 (Polychromatic418967fa.accept_19_10_7_3_1_6977 10 216
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 216 231 3 3 72 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 216 231
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 216 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 216 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 216 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 231 3 2 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 216 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 231
  (Polychromatic418967fa.accept_13_4_8_10_1_671 4 216 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 216 231 3 1 72 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 216 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 216 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 216 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 231)))))))))))))))) (allB_succ' 17 215 231
  (Eq.refl Bool.true) (allA_succ_of_accept 16 215 231 (accept_3_4 16 215 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 215 231 (Polychromatic418967fa.accept_22_15_17_11_1_10729 15 215 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  215 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 231 (accept_3_4 13
  215 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 231
  (Polychromatic418967fa.accept_9_3_8_6_1_80 12 215 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 215 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 231 (accept_3_4 10 215 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 215 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 215 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  215 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 231 (accept_3_4 7 215
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 215 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 215 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 215 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 231 (accept_3_4 4 215 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 215 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 215 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2
  215 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 231 (accept_3_4 1 215
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 231))))))))))))))))) (allB_succ' 18 214 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 231 (accept_3_5 17 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 214 231 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 214 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 214 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 214
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 231 (accept_3_5 14 214
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 231 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 231 (accept_3_5 11 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 231 (accept_3_5 8 214 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 214 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 231 (accept_3_5 5 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 214 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 214 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 231 (accept_3_5 2 214 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 231)))))))))))))))))) (allB_succ' 19 213 231
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 213 231 3 6 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 213 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 213 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 231
  (Polychromatic418967fa.accept_15_1_3_6_1_621 16 213 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 231 3 5 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 213
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 231 3 4 71 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 213 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 231 3 3 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 213 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 213 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 231 3 2 71 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 213 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 231 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 213
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 231 3 1 71 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 213 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 231))))))))))))))))))) (allB_succ' 20 212 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 212 231 (accept_3_4 19 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 212 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 212 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 231 (accept_3_4 16 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 231 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 212 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 231
  (Polychromatic418967fa.accept_13_1_4_10_1_622 14 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 212 231 (accept_3_4 13 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 212 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 212 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 231 (accept_3_4 10 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 212 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 212 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 212 231 (accept_3_4 7 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  212 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 212 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 231 (accept_3_4 4 212 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 212 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 231 (accept_3_4 1 212 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  231)))))))))))))))))))) (allB_succ' 21 211 231 (Eq.refl Bool.true) (allA_succ_of_accept 20 211 231 (accept_3_5 20 211
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 231 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 231
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 231 (accept_3_5 17 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 211 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 231 (accept_3_5 14 211 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 211
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 231 (accept_3_5 11 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 211 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 231 (accept_3_5 8 211 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 211 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 231
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 231 (accept_3_5 5 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 211 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 211 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 231 (accept_3_5 2 211 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 211 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 231))))))))))))))))))))) (allB_succ' 22 210 231
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 231 21 1 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 210 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 210 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 210 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 231 3 6 70 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 210 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 210 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 210 231 3 5 70 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 231 7 2 30 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 231 3 4 70 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 210 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 210 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 210 231 3 3 70 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 210 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 210 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 210 231 7 1 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 210 231 3 2 70 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 210 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 210 231 3 1 70 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 210 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 210 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 210 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 231)))))))))))))))))))))) (allB_succ' 23 209 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 209 231 11 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 209 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 209 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 231 (accept_3_4 19
  209 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 209 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 209 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 231 (accept_3_4 16 209 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 209 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 209 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 231 (accept_3_4 13 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 209 231 11 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 10 209 231 (accept_3_4 10 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 209 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 209 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 209 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 231 (accept_3_4 7 209 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 231 (accept_3_4 4 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 209 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 231 (accept_3_4 1 209 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 231))))))))))))))))))))))) (allB_succ' 24 208 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 208 231 (accept_3_5 23 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 208 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 208 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 208 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 208 231 (accept_3_5 20 208 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 208 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 208 231 (accept_3_5 17 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 208 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 208 231 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 231 (accept_3_5 14 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 208 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 208 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 208 231 (accept_3_5 11 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 208 231 (Polychromatic418967fa.accept_24_10_16_15_1_12045 10 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 231 (accept_3_5 8 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 208 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 231 (accept_3_5 5 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 208 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 208 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 231 (accept_3_5 2 208 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 231)))))))))))))))))))))))) (allB_succ' 25 207 231
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 207 231 3 8 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 207 231 (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 207 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 231
  (Polychromatic418967fa.accept_13_9_12_10_1_242 22 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 207 231 3 7 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 207 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 20 207 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 231 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 207
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 231 3 6 69 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 231
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 207 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 231 3 5 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 231 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 231
  (Polychromatic418967fa.accept_17_13_3_10_1_5157 13 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 207 231 3 4 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 207 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 207 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 231
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 207 231 3 3 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 207 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 207 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 231
  (Polychromatic418967fa.accept_13_7_12_10_1_640 7 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 207 231 3 2 69 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 231 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 207 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 207 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 231 3 1 69 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 231
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 207 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 231 (Polychromatic418967fa.accept_19_1_17_3_1_1821 1 207 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 231))))))))))))))))))))))))) (allB_succ' 26 206 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 206 231 (accept_3_4 25 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 206 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 206 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 231 (accept_3_4 22 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 206 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 231 (accept_3_4 19 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 231 (accept_3_4 16 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 206 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 231 (accept_3_4 13 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 231 (accept_3_4 10 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 231
  (Polychromatic418967fa.accept_13_8_11_10_1_636 8 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 231 (accept_3_4 7 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 231 (accept_3_4 4 206 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 206 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 231 (accept_3_4 1 206 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  231)))))))))))))))))))))))))) (allB_succ' 27 205 231 (Eq.refl Bool.true) (allA_succ_of_accept 26 205 231 (accept_3_5
  26 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 231
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 205 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 205 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 231 (accept_3_5 23 205 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 205 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 205 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 231 (accept_3_5 20
  205 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 231
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 205 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 231 (accept_3_5 17 205 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 205 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 205 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 231
  (Polychromatic418967fa.accept_20_15_5_11_1_8096 15 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 205 231 (accept_3_5 14 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 205 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 205 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 205 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 231 (accept_3_5 11 205 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 231
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 231 (accept_3_5 8 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 231 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 231 (accept_3_5 5 205 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 231 (accept_3_5 2 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 205 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 231))))))))))))))))))))))))))) (allB_succ' 28 204 231 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 204 231 3 9 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 204 231 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 204 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 204
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 231 3 8 68 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 231
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 231 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 204 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 204 231 3 7 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 204 231 (Polychromatic418967fa.accept_14_6_8_7_1_589
  20 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 231 3 6 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 204 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 204
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 204 231 3 5 68 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 204 231
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 231 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 204 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 231 3 4 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 231
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 204 231 3 3 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 204 231 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 204 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  7 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 231 3 2 68 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 231
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 204 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 204 231 3 1 68 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 231 (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 204 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 231
  (Polychromatic418967fa.accept_13_1_9_10_1_625 1 204 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 231)))))))))))))))))))))))))))) (allB_succ' 29 203 231 (Eq.refl Bool.true) (allA_succ_of_gcd 28 203 231
  7 4 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 203
  231 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 203 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 231 (accept_3_4 25 203 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 203 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 231
  (Polychromatic418967fa.accept_17_6_16_10_1_2890 23 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 203 231 (accept_3_4 22 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 203 231 7 3 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 203 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 203 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 231 (accept_3_4 19 203 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 203 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 203 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 231 (accept_3_4 16 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 203 231 7 2 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 203 231 (accept_3_4 13 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 203 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 203 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 231 (accept_3_4 10 203 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 231 (Polychromatic418967fa.accept_12_9_11_3_1_772
  9 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 203 231 7 1 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 203 231 (Polychromatic418967fa.accept_17_6_16_10_1_2890 6 203 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 203
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 231 (accept_3_4 4 203 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 231 (accept_3_4 1 203 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  231))))))))))))))))))))))))))))) (allB_succ' 30 202 231 (Eq.refl Bool.true) (allA_succ_of_accept 29 202 231
  (accept_3_5 29 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 202 231
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 202 231 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 202 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 231 (accept_3_5 26 202 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 202 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 231
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 231 (accept_3_5 23 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 231 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 231 (accept_3_5 20 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 202 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 231 (accept_3_5 17 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 202 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 231 (accept_3_5 14 202 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 231 (accept_3_5 11 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 231 (accept_3_5 8 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 202 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 231 (accept_3_5 5 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 231 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 202 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 231 (accept_3_5 2 202 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 231)))))))))))))))))))))))))))))) (allB_succ' 31 201
  231 (Eq.refl Bool.true) (allA_succ_of_gcd 30 201 231 3 10 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 201 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 201 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 201 231 3 9 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 201 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 201 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 231 3 8 67 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 231 3 7 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 201 231 3 6 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 201 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 201 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 231 3 5 67 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 231 3 4 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 201 231 3 3 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 201 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 201 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 231 3 2 67 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 201 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 231 3 1 67 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 201 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 231))))))))))))))))))))))))))))))) (allB_succ' 32 200 231 (Eq.refl Bool.true) (allA_succ_of_accept 31
  200 231 (accept_3_4 31 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 200 231
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 200 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 200 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 231 (accept_3_4 28 200 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 200 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 200 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 231 (accept_3_4 25 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 231 (accept_3_4 22 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 200 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 231
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 231 (accept_3_4 19 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 231 (accept_3_4 16 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 200 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 231 (accept_3_4 13 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 231 (accept_3_4 10 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 231 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 200 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 231 (accept_3_4 7 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 231 (accept_3_4 4 200 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 200 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 231
  (Polychromatic418967fa.accept_13_2_5_10_1_250 2 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 231 (accept_3_4 1 200 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  231)))))))))))))))))))))))))))))))) (allB_succ' 33 199 231 (Eq.refl Bool.true) (allA_succ_of_accept 32 199 231
  (accept_3_5 32 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 199 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 199 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 231 (accept_3_5 29 199 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 199 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 231 (Polychromatic418967fa.accept_13_1_4_10_1_622
  27 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 231 (accept_3_5 26
  199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 231
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 199 231 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 231 (accept_3_5 23 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 199 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 231 (accept_3_5 20 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 231 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 199 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 231 (accept_3_5 17 199 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 199 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 231 (accept_3_5 14 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 231 (accept_3_5 11 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 199 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 231
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 231 (accept_3_5 8 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 231 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 231 (accept_3_5 5 199 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 199 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 231 (accept_3_5 2 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 199 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 231))))))))))))))))))))))))))))))))) (allB_succ' 34 198 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 198 231 33 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 198 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 198
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 231 3 10 66 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 198 231 3 9 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 198 231 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 231 3 8 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 231 11 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 231 3 7 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 198 231 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 231
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 231 3 6 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 198 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 198
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 198 231 3 5 66 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 198 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 231 3 4 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 198 231 11 1 18 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 198 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 198 231 3 3 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 198 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 231 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 198 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 231 3 2 66 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 198 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 231 3 1 66 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 198 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 231)))))))))))))))))))))))))))))))))) (allB_succ' 35 197 231 (Eq.refl Bool.true) (allA_succ_of_accept 34
  197 231 (accept_3_4 34 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 231
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 197 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 197 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 231 (accept_3_4 31 197 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 231 (accept_3_4 28
  197 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 231
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 231 (accept_3_4 25 197 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 197 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 197 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 231 (accept_3_4 22 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 231 (accept_3_4 19 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 231
  (Polychromatic418967fa.accept_27_17_8_15_1_2268 17 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 197 231 (accept_3_4 16 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 197 231 (Polychromatic418967fa.accept_19_15_7_3_1_4143 15 197 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 231 (accept_3_4 13 197 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 231 (accept_3_4 10 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 231 (accept_3_4 7 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 231 (accept_3_4 4 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 197 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 231 (accept_3_4 1 197 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 231))))))))))))))))))))))))))))))))))) (allB_succ' 36 196 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 196 231 7 5 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 196 231 (Polychromatic418967fa.accept_23_11_12_1_1_13862 34 196 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 231 (Polychromatic418967fa.accept_15_3_1_6_1_206
  33 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 231 (accept_3_5 32
  196 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 196 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 196 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 196 231 (accept_3_5 29 196 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 196 231 7 4 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 196 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 196 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 231 (accept_3_5 26 196 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 196 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 231
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 231 (accept_3_5 23 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 196 231 7 3 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 196 231 (accept_3_5 20 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 196 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 196 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 196
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 231 (accept_3_5 17 196
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 231
  (Polychromatic418967fa.accept_17_16_9_10_1_3962 16 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 196 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 231 7 2 28 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 13 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 196 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 196 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 231 (accept_3_5 11 196 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 196 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 196 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 231 (Polychromatic418967fa.accept_13_9_1_10_1_647
  9 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 231 (accept_3_5 8
  196 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 196 231 7 1 28 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 196 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 231 (accept_3_5 5 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 196 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 196 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 231 (accept_3_5 2 196 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 231)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 195 231 (Eq.refl Bool.true) (allA_succ_of_gcd 36 195 231 3 12 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 195 231 (Polychromatic418967fa.accept_19_16_5_3_1_1813
  35 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 34 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 195 231 3 11 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 195 231 (Polychromatic418967fa.accept_17_15_8_10_1_2886 32 195 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 231
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 195 231 3 10 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 195 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 195 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 195 231 3 9 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 195 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 231 (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 195
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 195 231 3 8 65 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 231
  (Polychromatic418967fa.accept_22_1_19_11_1_12229 23 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 195 231 (Polychromatic418967fa.accept_14_8_13_7_1_2798 22 195 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 195 231 3 7 65 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 195 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 231 3 6 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 231 (Polychromatic418967fa.accept_19_17_5_3_1_5455
  17 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 16 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 231 3 5 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 195 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 231 (Polychromatic418967fa.accept_20_13_15_11_1_6610 13
  195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 231 3 4 65 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 231
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 231 (Polychromatic418967fa.accept_16_10_3_7_1_8094 10 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 231 3 3 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 231 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 195 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 231
  (Polychromatic418967fa.accept_19_7_5_3_1_13861 7 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 195 231 3 2 65 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 195 231 (Polychromatic418967fa.accept_20_5_15_11_1_3758 5 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 195 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 231 3 1 65 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 231
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 2 195 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 231 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 195 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195 231))))))))))))))))))))))))))))))))))))) (allB_succ' 38 194 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 231 (accept_3_4 37 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 194 231 (Polychromatic418967fa.accept_23_13_10_1_1_7182 36 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 194 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35
  194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 231 (accept_3_4 34
  194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 194 231 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 194 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 194 231 (accept_3_4 31 194 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 194 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 194 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 231 (accept_3_4 28
  194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 194 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 194 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 194 231 (accept_3_4 25 194 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 194 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 194 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 194 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 194 231 (accept_3_4 22 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 194 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 194 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 231 (accept_3_4 19 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 194 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 194 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 194 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 194 231 (accept_3_4 16 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 194 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 194 231 (Polychromatic418967fa.accept_17_14_7_10_1_7808 14 194 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 231 (accept_3_4 13 194 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 194 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 231 (accept_3_4 10 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 231 (accept_3_4 7 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 194 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 231 (accept_3_4 4 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 194 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 231 (accept_3_4 1 194 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 231)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 193 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 193 231 (accept_3_5 38 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 193 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 193 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 231 (Polychromatic418967fa.accept_24_12_1_15_1_12071 36
  193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 231 (accept_3_5 35
  193 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 193 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 193 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 231 (accept_3_5 32 193 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 193 231 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 231 (accept_3_5 29 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 231 (accept_3_5 26 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 193 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 231
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 193 231 (accept_3_5 23 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 193 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 193 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 231 (accept_3_5 20 193 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19
  193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 231 (accept_3_5 17 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 231 (accept_3_5 14 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 231 (Polychromatic418967fa.accept_22_13_17_11_1_5908 13
  193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 231 (accept_3_5 11 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 193 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 231 (accept_3_5 8 193 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 231 (accept_3_5 5 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 193 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 231 (accept_3_5 2 193 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 193 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 231)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 192 231 (Eq.refl Bool.true) (allA_succ_of_gcd 39 192 231 3 13 64 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 192 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 231 3 12 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 192 231 3 11 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 192 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 192 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 231 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 231 3 10 64 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 192 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 192 231 3 9 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 192 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 231 3 8 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 192 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 192 231 3 7 64 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 192 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 231 3 6 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 192 231 3 5 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 192 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 192 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 231 3 4 64 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 192 231 3 3 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 192 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 192 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 231 3 2 64 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 192 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 192 231 3 1 64 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 192 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 192 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 192 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 231)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 191 231
  (Eq.refl Bool.true) (allA_succ_of_accept 40 191 231 (accept_3_4 40 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 191 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 191 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 191 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 231 (accept_3_4 37 191 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 231
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 191 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 191 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 231 (accept_3_4 34 191 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 191 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 231 (accept_3_4 31 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 231 (Polychromatic418967fa.accept_19_10_1_3_1_12548 29 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 231 (accept_3_4 28 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 191
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 231 (accept_3_4 25 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 231 (accept_3_4 22 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 231 (accept_3_4 19 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 231 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 231 (accept_3_4 16 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 231 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 191 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 231 (accept_3_4 13 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 231 (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 231 (accept_3_4 10 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 191 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 231 (accept_3_4 7 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 231 (accept_3_4 4 191 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 191 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 231 (accept_3_4 1 191 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  231))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 190 231 (Eq.refl Bool.true) (allA_succ_of_accept 41 190
  231 (accept_3_5 41 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 190 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 190 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 190 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 231 (accept_3_5 38 190 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 231
  (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 190 231 (accept_3_5 35 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 190 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 231 (accept_3_5 32 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 190 231 (accept_3_5 29 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 190 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 190 231 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 190 231 (accept_3_5 26 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 190 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 190 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 24 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 190 231 (accept_3_5 23 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 231 (accept_3_5 20 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 231 (accept_3_5 17 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 231 (accept_3_5 14 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 231 (accept_3_5 11 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 231 (Polychromatic418967fa.accept_16_10_14_7_1_2372 10 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 231 (accept_3_5 8 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 231 (accept_3_5 5 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 190 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 231 (accept_3_5 2 190 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 231))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 189 231 (Eq.refl Bool.true) (allA_succ_of_gcd 42 189 231 21 2 9 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 189 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 231 (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 189 231 3 13 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 189 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 189 231 3 12 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 189 231 7 5 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 189 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 189 231 3 11 63 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 189 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 189 231 3 10 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 189 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 189 231 7 4 27 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 189 231 3 9 63 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 189 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 231 3 8 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 189 231 21 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 189 231 (Polychromatic418967fa.accept_16_4_13_7_1_4522 20 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 189
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 231 3 6 63 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 231 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 231 3 5 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 189 231 7 2 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 189 231 (Polychromatic418967fa.accept_12_1_9_3_1_370
  13 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 231 3 4 63 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 231 3 3 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 189 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 189 231 7 1 27 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 189 231 3 2 63 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 231 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 189 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 231 3 1 63 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 189 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 231))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 188 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 188 231 (accept_3_4 43 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 231 (accept_3_4 40 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 231 (accept_3_4 37 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 231 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 231 (accept_3_4 34 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 231 (accept_3_4 31 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 231 (accept_3_4 28 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 231
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 188 231 (accept_3_4 25 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 188 231 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 231 (accept_3_4 22 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 188 231 (accept_3_4 19 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 188 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 231 (accept_3_4 16 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 188 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 188 231 (accept_3_4 13 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 188 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 231 (accept_3_4 10 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 231
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 231 (accept_3_4 7 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 231 (accept_3_4 4 188 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 188 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 231 (accept_3_4 1 188 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  231)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 187 231 (Eq.refl Bool.true) (allA_succ_of_gcd 44 187
  231 11 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  187 231 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 187 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 231 (accept_3_5 41 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 187 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 231 (accept_3_5 38 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 231 (accept_3_5 35 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 187 231 11 3 17 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 187 231 (accept_3_5 32 187 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 231 (Polychromatic418967fa.accept_9_4_7_6_1_255
  31 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 231 (accept_3_5 29 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 231 (accept_3_5 26 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 231 (Polychromatic418967fa.accept_19_6_16_3_1_1801 25 187
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 231 (accept_3_5 23 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  187 231 11 2 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 187 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 187 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 231 (accept_3_5 20 187 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 187 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 231
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 231 (accept_3_5 17 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 231 (accept_3_5 14 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 187 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 187 231 11 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 231 (accept_3_5 8
  187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 231
  (Polychromatic418967fa.accept_24_7_19_15_1_12097 7 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 231 (accept_3_5 5 187 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 231 (accept_3_5 2 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 187 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 231))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 186 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 186 231 3 15 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 186 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 186 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 231
  (Polychromatic418967fa.accept_17_9_16_10_1_362 43 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 231 3 14 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 186 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  40 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 186 231 3 13 62 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 186 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 186 231 3 12 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 186 231 (Polychromatic418967fa.accept_10_5_6_1_1_836
  35 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 186 231 3 11 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 186 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 186 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 231
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 231 3 10 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 186 231 3 9 62 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 186 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 231 3 8 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 231
  (Polychromatic418967fa.accept_17_6_16_10_1_2890 23 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 186 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 186 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 186 231 3 7 62 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 186 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 231 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 186 231 3 6 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 186 231 3 5 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 186 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 186 231 3 4 62 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 186 231
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 186 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 186 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 186 231 3 3 62 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 186 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 231 3 2 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 186 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 186 231 3 1 62 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 186 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 186 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  231)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 185 231 (Eq.refl Bool.true) (allA_succ_of_accept 46
  185 231 (accept_3_4 46 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 231
  (Polychromatic418967fa.accept_12_9_5_3_1_782 45 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 185 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 231 (accept_3_4 43 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 231 (Polychromatic418967fa.accept_13_2_3_10_1_658
  41 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 231 (accept_3_4 40
  185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 231 (accept_3_4 37 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 185 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 185 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 231 (accept_3_4 34 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 231 (accept_3_4 31 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 185 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 231 (accept_3_4 28 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 231 (accept_3_4 25 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 185 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 231
  (Polychromatic418967fa.accept_29_23_11_28_1_13860 23 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 185 231 (accept_3_4 22 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 185 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 185 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 231 (accept_3_4 19 185 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 231 (accept_3_4 16 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 231 (accept_3_4 13 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 185 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 231 (accept_3_4 10 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 231 (accept_3_4 7 185 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 231
  (Polychromatic418967fa.accept_17_5_15_10_1_10176 5 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 185 231 (accept_3_4 4 185 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 185 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 185 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 231 (accept_3_4 1 185 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 231))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 184 231 (Eq.refl Bool.true) (allA_succ_of_accept 47 184 231 (accept_3_5 47 184 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 184 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 184 231 (Polychromatic418967fa.accept_10_5_4_1_1_842
  45 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 231 (accept_3_5 44
  184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 184 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 184 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 184 231 (accept_3_5 41 184 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 184 231 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 184 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 184 231 (accept_3_5 38 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 184 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 184 231 (accept_3_5 35 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 184 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 184 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 184 231
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 184 231 (accept_3_5 32 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 184 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 231 (accept_3_5 29 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 184 231 (accept_3_5 26 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 231 (accept_3_5 23 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 231 (Polychromatic418967fa.accept_17_5_14_10_1_2831 22 184
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 231 (accept_3_5 20 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 231 (accept_3_5 17 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 184 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 231
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 231 (accept_3_5 14 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 231 (accept_3_5 11 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 231
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 231 (accept_3_5 8 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 231 (accept_3_5 5 184 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 184 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 231 (accept_3_5 2 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 231)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 183 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 183 231 3 16 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 183 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 231 3 15 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 183 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 183 231 3 14 61 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 183 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 231 3 13 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 231 3 12 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 183 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 183 231 3 11 61 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 183 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 231 3 10 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 231 3 9 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 183 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 231 3 8 61 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 231 3 7 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 231 3 6 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 183 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 231 3 5 61 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 231 3 4 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 231 3 3 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 231 3 2 61 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 183 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 231 3 1 61 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 183 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 231))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 182 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 182 231 7 7 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 182 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 182 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 182 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 182 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 231 (accept_3_4 46 182 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 231 (accept_3_4 43 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  182 231 7 6 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 182 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 182 231 (accept_3_4 40 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 182 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 182 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 231 (Polychromatic418967fa.accept_15_8_2_6_1_2125 38 182
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 182 231 (accept_3_4 37 182
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 182 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 182 231 7 5 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 182 231 (accept_3_4 34 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 182 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 182 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 182 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 182 231 (accept_3_4 31 182 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 182 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 182 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 182 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 182 231 7 4 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 182 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 182 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 182 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 231 (accept_3_4 25 182 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 231
  (Polychromatic418967fa.accept_22_2_6_11_1_13859 24 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 182 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 182 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 231 (accept_3_4 22 182 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 182 231 7 3 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 182 231 (Polychromatic418967fa.accept_19_1_11_3_1_5463 20 182
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 231 (accept_3_4 19 182
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 231
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 182 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 231 (accept_3_4 16 182 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 182 231 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 182 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 182 231 7 2 26 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 182 231 (accept_3_4 13 182 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 182 231 (Polychromatic418967fa.accept_9_3_2_6_1_264
  12 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 182 231 (accept_3_4 10 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  182 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 182 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 182 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 182 231 7 1 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 182 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 182 231 (accept_3_4 4 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  182 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 182 231 (Polychromatic418967fa.accept_17_2_12_10_1_9034 2 182 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 231 (accept_3_4 1 182 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 182 231)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 181
  231 (Eq.refl Bool.true) (allA_succ_of_accept 50 181 231 (accept_3_5 50 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 181 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 181 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 48
  181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 231 (accept_3_5 47
  181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 181 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 231 (accept_3_5 44 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 181 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 181 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 231 (accept_3_5 41
  181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 181 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 231 (accept_3_5 38 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 181 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 231
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 181 231 (accept_3_5 35 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 181 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 231 (accept_3_5 32 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 231 (accept_3_5 29 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 231 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 231 (accept_3_5 26 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 181 231 (accept_3_5 23 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 231 (accept_3_5 20 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 231
  (Polychromatic418967fa.accept_13_6_12_10_1_690 19 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 231 (accept_3_5 17 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 181 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 231
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 181 231 (accept_3_5 14 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 181 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 231 (accept_3_5 11 181 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 231 (accept_3_5 8 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 231 (accept_3_5 5 181 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 231 (accept_3_5 2 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 231 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 181 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 231))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 180 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 180 231 3 17 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 180 231 (Polychromatic418967fa.accept_19_12_9_3_1_13858 50 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 180 231
  (Polychromatic418967fa.accept_19_11_9_3_1_4167 49 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 231 3 16 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 47 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 180 231
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 46 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 180 231 3 15 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 180 231 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 231 3 14 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 231
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 180 231 3 13 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 180 231 (Polychromatic418967fa.accept_13_12_11_10_1_2711 38 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 231
  (Polychromatic418967fa.accept_14_9_12_7_1_597 37 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 231 3 12 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 180 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 180 231
  (Polychromatic418967fa.accept_13_8_11_10_1_636 34 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 180 231 3 11 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 180 231 (Polychromatic418967fa.accept_19_13_9_3_1_9806 32 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 231
  (Polychromatic418967fa.accept_19_12_9_3_1_13858 31 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 180 231 3 10 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 180 231 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 231
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 180 231 3 9 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 180 231 (Polychromatic418967fa.accept_25_1_5_6_1_13857 26 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 231
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 231 3 8 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 23 180 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 231
  (Polychromatic418967fa.accept_25_22_5_6_1_10417 22 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 180 231 3 7 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 180 231 (Polychromatic418967fa.accept_23_20_19_1_1_13856 20 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 231 3 6 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 180 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 231
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 180 231 3 5 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 180 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 231
  (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 231 3 4 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 180 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 180 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 231 (Polychromatic418967fa.accept_19_10_9_3_1_7009 10 180
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 180 231 3 3 60 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 180 231
  (Polychromatic418967fa.accept_13_8_11_10_1_636 8 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 231 (Polychromatic418967fa.accept_22_7_4_11_1_9131 7 180 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 231 3 2 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 231 (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 180 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 231
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 180 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 180 231 3 1 60 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 180 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 180 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 180
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  231)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 179 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 179 231 (accept_3_4 52 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 179 231 (Polychromatic418967fa.accept_19_13_8_3_1_2906 51 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 231 (accept_3_4 49 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 231 (accept_3_4 46 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 231 (accept_3_4 43 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 231 (accept_3_4 40 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 231 (accept_3_4 37 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 231 (accept_3_4 34 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 231 (accept_3_4 31 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 231 (accept_3_4 28 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 231 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 231 (accept_3_4 25 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 231 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 179 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 231 (accept_3_4 22 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 231 (accept_3_4 19 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 231
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 231 (accept_3_4 16 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 231 (accept_3_4 13 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 231 (accept_3_4 10 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 231 (accept_3_4 7 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 231 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 179 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 231 (accept_3_4 4 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 179 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 231 (accept_3_4 1 179 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 231))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 178 231
  (Eq.refl Bool.true) (allA_succ_of_accept 53 178 231 (accept_3_5 53 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 178 231 (Polychromatic418967fa.accept_15_7_13_6_1_696 52 178 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 178 231 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 178
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 178 231 (accept_3_5 50 178
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9
  49 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 178 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 178 231 (accept_3_5 47 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 178 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 178 231 (accept_3_5 44 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 178 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 178 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 178 231 (accept_3_5 41 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 178 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 178 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 178 231 (accept_3_5 38 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 178 231
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 178 231 (accept_3_5 35 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 178 231 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 231 (accept_3_5 32 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 178 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 178 231 (accept_3_5 29 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 178 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 178 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 231 (accept_3_5 26 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 231
  (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 178 231 (accept_3_5 23 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 178 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 178 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 231 (accept_3_5 20 178 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 231 (accept_3_5 17 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 231 (Polychromatic418967fa.accept_20_16_18_11_1_9605 16 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 231 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 178 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 231 (accept_3_5 14 178 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 231 (accept_3_5 11 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 231 (accept_3_5 8 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 231 (accept_3_5 5 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 178 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 231 (accept_3_5 2 178 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 177 231 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 177 231 3 18 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 177 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 177
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 231 3 17 59 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 177 231 3 16 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 177 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 231 3 15 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 177 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 231 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 177 231 3 14 59 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 177 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 231 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 177 231 3 13 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 177 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 231 3 12 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 177 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 231 3 11 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 177 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 231 3 10 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 177 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 177 231 3 9 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 177 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 177
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 231 3 8 59 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 231 3 7 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663
  20 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 177 231 3 6 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 177 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 177
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 231 3 5 59 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 231 3 4 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 231 3 3 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 231 (Polychromatic418967fa.accept_16_8_1_7_1_2355 8 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 177 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 231 3 2 59 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 177 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 231 3 1 59 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 177 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 231))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 176 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 176 231 11 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 176 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 176 231 (accept_3_4 52
  176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 176 231
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 176 231 (Polychromatic418967fa.accept_15_5_11_6_1_692 50 176 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 176 231 (accept_3_4 49 176 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 176 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 176 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 176 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 176 231 (accept_3_4 46 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 176 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 176 231 11 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 176 231 (accept_3_4 43 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 176 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 176 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 231 (accept_3_4 40 176 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 231 (Polychromatic418967fa.accept_9_3_5_6_1_253
  39 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 231 (accept_3_4 37 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 231 (Polychromatic418967fa.accept_19_17_5_3_1_5455 36 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 231 (accept_3_4 34 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 176 231 11 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 176 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 176
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 176 231 (accept_3_4 31 176
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 231 (accept_3_4 28 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 176 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 176 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 231 (accept_3_4 25 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 231 11 2 16 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 176 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 231 (accept_3_4 19 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 176 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 231 (accept_3_4 16
  176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 176 231 (Polychromatic418967fa.accept_19_14_5_3_1_859 14 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 231 (accept_3_4 13 176 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 176 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 176 231 11 1 16 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 176 231 (accept_3_4 10 176 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 176 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 231 (accept_3_4 7 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 231 (accept_3_4 4 176 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 176 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 231 (accept_3_4 1 176 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 175 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 175 231 7 8 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 175 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 231 (accept_3_5 53 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 175 231 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 231 (accept_3_5 50 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 175 231 7 7 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 175 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 175 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 231 (accept_3_5 47 175 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 231
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 231 (accept_3_5 44 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 175 231 7 6 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 175 231 (accept_3_5 41 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 231 (accept_3_5 38 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37
  175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 175 231 7 5 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 231 (accept_3_5 32 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 231
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 175 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 231 (accept_3_5 29 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 175 231 7 4 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 175 231 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 231 (accept_3_5 26 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 231 (Polychromatic418967fa.accept_9_7_4_6_1_273
  25 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 231 (accept_3_5 23 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 175 231 7 3 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 175 231 (accept_3_5 20 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 175 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 231 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 231 (accept_3_5 17 175
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 175 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 175 231 7 2 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 231
  (Polychromatic418967fa.accept_17_13_5_10_1_2839 13 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 175 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 231 (accept_3_5 11 175 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 175 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 231
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 231 (accept_3_5 8 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175
  231 7 1 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  175 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 175 231 (accept_3_5 5 175 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 175 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 231 (accept_3_5 2 175 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1
  175 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 174 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 174 231 3 19 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 174 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 231 3 18 58 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 174 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 174 231 3 17 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 174 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 231 3 16 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 174 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 174 231 3 15 58 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 174 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 174 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 231 3 14 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 174 231 3 13 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 174 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 174 231 3 12 58 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 174 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 174 231 3 11 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 174 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 231 3 10 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 174 231 3 9 58 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 174 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 174 231 3 8 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 174 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 174 231 3 7 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 174 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 231 3 6 58 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 174 231 3 5 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 174 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 231 3 4 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 174 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 231 3 3 58 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 231 3 2 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 174 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 174 231 3 1 58 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 174 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 174 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 173 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 173 231 (accept_3_4 58 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 231 (accept_3_4 55 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 231 (accept_3_4 52 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 231 (Polychromatic418967fa.accept_14_9_5_7_1_1251 51 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 231 (accept_3_4 49 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 231
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 231 (accept_3_4 46 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 231 (accept_3_4 43 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 231 (accept_3_4 40 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 231 (accept_3_4 37 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 231 (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 173 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 231 (accept_3_4 34 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 231 (accept_3_4 31 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 231
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 231 (accept_3_4 28 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 231 (accept_3_4 25 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 231 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 173 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 231 (accept_3_4 22 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 231 (accept_3_4 19 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 231 (accept_3_4 16 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 231 (Polychromatic418967fa.accept_20_15_13_11_1_5110 15 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 231 (accept_3_4 13 173 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 231
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 173 231 (accept_3_4 10 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 173 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 173 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 231 (accept_3_4 7 173 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 231 (accept_3_4 4 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 173 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 231 (accept_3_4 1 173 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 172
  231 (Eq.refl Bool.true) (allA_succ_of_accept 59 172 231 (accept_3_5 59 172 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 172 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 57
  172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 172 231 (accept_3_5 56
  172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 172 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 172 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 172 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 231 (accept_3_5 53 172 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 172 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 172 231 (Polychromatic418967fa.accept_8_3_4_7_1_475
  51 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 172 231 (accept_3_5 50
  172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 172 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 172 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 172 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 231 (accept_3_5 47 172 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 172 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 231
  (Polychromatic418967fa.accept_13_6_3_10_1_698 45 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 172 231 (accept_3_5 44 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 172 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 231 (accept_3_5 41 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 172 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 231 (accept_3_5 38 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 231 (accept_3_5 35 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 172 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 231
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 231 (accept_3_5 32 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 231 (accept_3_5 29 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 231 (accept_3_5 26 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 231 (accept_3_5 23 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 172 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 231 (accept_3_5 20 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 231 (accept_3_5 17 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 172 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 231
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 231 (accept_3_5 14 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 231 (accept_3_5 11 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 172 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 231
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 231 (accept_3_5 8 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 231 (accept_3_5 5 172 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 172 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 231 (accept_3_5 2 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 171 231
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 171 231 3 20 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 231 (Polychromatic418967fa.accept_18_5_9_15_1_4695 59 171
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 231
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 58 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 171 231 3 19 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 171 231 (Polychromatic418967fa.accept_27_2_9_15_1_13855 56 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 231
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 55 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 231 3 18 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 171 231 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 171 231 3 17 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 171 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 50 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 231
  (Polychromatic418967fa.accept_22_5_17_11_1_5880 49 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 171 231 3 16 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 171 231 (Polychromatic418967fa.accept_13_8_2_10_1_652 47 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 231
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 46 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 231 3 15 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 171 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 171 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 231
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 43 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 171 231 3 14 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 171 231 (Polychromatic418967fa.accept_17_7_1_10_1_2836 41 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 231
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 231 3 13 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 171 231 (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 231
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 171 231 3 12 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 171 231 (Polychromatic418967fa.accept_16_3_11_7_1_770 35 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 231
  (Polychromatic418967fa.accept_13_8_2_10_1_652 34 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 171 231 3 11 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 171 231 (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 231
  (Polychromatic418967fa.accept_13_5_2_10_1_248 31 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 231 3 10 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 231 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 171 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 171 231 3 9 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 231 (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 171 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 231 (Polychromatic418967fa.accept_13_12_2_10_1_2698 25 171
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 231 3 8 57 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 231
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 231 (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 171 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 231 3 7 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20
  171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 231
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 171 231 3 6 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 231 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 171 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 231
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 231 3 5 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 231 (Polychromatic418967fa.accept_17_14_1_10_1_3941 14 171 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 231
  (Polychromatic418967fa.accept_22_13_17_11_1_5908 13 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 171 231 3 4 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 171 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 171 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 231
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 10 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 231 3 3 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 231 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 171 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 231 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 171
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 231 3 2 57 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 231
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 171 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 231 3 1 57 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 231 (Polychromatic418967fa.accept_16_2_11_7_1_2352 2 171 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 231
  (Polychromatic418967fa.accept_27_1_9_15_1_13854 1 171 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 170 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 231 (accept_3_4 61 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 170 231 (Polychromatic418967fa.accept_23_14_9_1_1_13853 60 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 170 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59
  170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 170 231 (accept_3_4 58
  170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 170 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 170 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 170 231 (accept_3_4 55 170 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 170 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 170 231 (accept_3_4 52 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 170 231 (Polychromatic418967fa.accept_14_9_2_7_1_1242 51 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 170 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 170 231 (accept_3_4 49 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 170 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 170 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 170 231 (accept_3_4 46 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 170 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 170 231 (Polychromatic418967fa.accept_15_14_5_6_1_6168 44 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 170 231 (accept_3_4 43 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 170 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 170
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 170 231 (accept_3_4 40 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 170 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 170 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 231 (accept_3_4 37 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 231 (Polychromatic418967fa.accept_25_11_20_6_1_13788 36 170 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 170 231 (accept_3_4 34 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 170 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 170 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 231 (accept_3_4 31 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 170 231 (accept_3_4 28 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 170 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 170 231 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 231 (accept_3_4 25 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 170
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 170 231 (accept_3_4 22 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 170 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 170 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 231 (accept_3_4 19 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 170 231 (accept_3_4 16 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 170 231 (Polychromatic418967fa.accept_19_15_18_3_1_1807 15 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 170 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 231 (accept_3_4 13 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 170 231 (accept_3_4 10 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  170 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 170 231 (Polychromatic418967fa.accept_23_8_9_1_1_13852 8 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 231 (accept_3_4 7 170 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 170 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 170 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 170 231 (accept_3_4 4 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  170 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 170 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 170 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 231 (accept_3_4 1 170 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  169 231 (Eq.refl Bool.true) (allA_succ_of_accept 62 169 231 (accept_3_5 62 169 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 169 231 (Polychromatic418967fa.accept_16_13_9_7_1_4532 61 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 231
  (Polychromatic418967fa.accept_17_9_16_10_1_362 60 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 231 (accept_3_5 59 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 231 (accept_3_5 56 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 231 (accept_3_5 53 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 231 (Polychromatic418967fa.accept_16_3_9_7_1_6842 51 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 231 (accept_3_5 50 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 169 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 231 (accept_3_5 47 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 231 (accept_3_5 44 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 231 (Polychromatic418967fa.accept_15_13_4_6_1_3046 43 169
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 231 (accept_3_5 41 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 231 (accept_3_5 38 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 231
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 231 (accept_3_5 35 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 231 (accept_3_5 32 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 169 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 231 (accept_3_5 29 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 231 (accept_3_5 26 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 169
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 231
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 231 (accept_3_5 23 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 231 (accept_3_5 20 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 231 (accept_3_5 17 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 231 (accept_3_5 14 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 169 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 231 (accept_3_5 11 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 231 (accept_3_5 8 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 231 (Polychromatic418967fa.accept_17_7_16_10_1_1849 7 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 231 (accept_3_5 5 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 231 (accept_3_5 2 169 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 168 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 168 231 21 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 168 231 (Polychromatic418967fa.accept_19_5_16_3_1_1820 62 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 231 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 168
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 231 3 20 56 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 231
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 168 231 (Polychromatic418967fa.accept_13_6_12_10_1_690 58 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 168 231 3 19 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 231 7 8 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 231 (Polychromatic418967fa.accept_15_10_3_6_1_3042
  55 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 231 3 18 56 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 231
  (Polychromatic418967fa.accept_10_3_8_1_1_182 53 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 168 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 168 231 3 17 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 168 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 168 231 7 7 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 48 168 231 3 16 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 168
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 231
  (Polychromatic418967fa.accept_13_7_12_10_1_640 46 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 168 231 3 15 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 168 231 (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 168 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 231
  (Polychromatic418967fa.accept_10_3_8_1_1_182 43 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 231 21 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 168 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 231
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 168 231 3 13 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 168 231 (Polychromatic418967fa.accept_17_4_15_10_1_5139 38 168 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 231 3 12 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 168 231 7 5 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 168 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 168 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 168 231 3 11 56 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 168 231
  (Polychromatic418967fa.accept_13_6_12_10_1_690 32 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 168 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 231 3 10 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  29 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 231 7 4 24 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 231 3 9 56 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 168 231
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 168 231 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 231 3 8 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 231 (Polychromatic418967fa.accept_10_3_8_1_1_182
  23 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 231
  (Polychromatic418967fa.accept_13_9_12_10_1_242 22 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 168 231 21 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 168 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 20 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 168
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 231 3 6 56 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 231
  (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 231 3 5 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 231 7 2 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 231 (Polychromatic418967fa.accept_10_3_8_1_1_182
  13 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 231 3 4 56 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 231 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 168 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 231 3 3 56 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 231
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 168 231 7 1 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 168 231 3 2 56 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 231 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 168 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 231 3 1 56 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 231
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 168 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 168 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 167 231 (Eq.refl Bool.true) (allA_succ_of_accept 64 167 231 (accept_3_4 64 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 231 (Polychromatic418967fa.accept_18_9_5_15_1_2246 63 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 167 231 (accept_3_4 61 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 231 (Polychromatic418967fa.accept_24_11_23_15_1_12139 59 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 231 (accept_3_4 58 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 231 (accept_3_4 55 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 231 (accept_3_4 52 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 231 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 231 (accept_3_4 49 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 231 (accept_3_4 46 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 231 (accept_3_4 43 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 231 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 231 (accept_3_4 40 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 231 (accept_3_4 37 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 231 (accept_3_4 34 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 231 (accept_3_4 31 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 231 (accept_3_4 28 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 231 (accept_3_4 25 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 231 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 231 (accept_3_4 22 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 231 (accept_3_4 19 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 231 (Polychromatic418967fa.accept_17_1_14_10_1_10151 18 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 231 (accept_3_4 16 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 167
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 231 (accept_3_4 13 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 231 (accept_3_4 10 167 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 231 (accept_3_4 7 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 231 (Polychromatic418967fa.accept_17_5_14_10_1_2831 5 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 231 (accept_3_4 4 167 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 167 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 231 (accept_3_4 1 167 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 166 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 166 231 (accept_3_5 65 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 166 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 166 231 (Polychromatic418967fa.accept_15_3_1_6_1_206 63 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 166 231 (accept_3_5 62 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 166 231
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 60 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 166 231 (accept_3_5 59 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 166 231 (Polychromatic418967fa.accept_14_2_12_7_1_617 58 166 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 166 231 (accept_3_5 56 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 166 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 166 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 166 231 (accept_3_5 53 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 166 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 166 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 231 (accept_3_5 50 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 166 231 (accept_3_5 47 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 166 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 231 (accept_3_5 44 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 231 (accept_3_5 41 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 231 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 231 (accept_3_5 38 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 231
  (Polychromatic418967fa.accept_19_17_14_3_1_5572 36 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 166 231 (accept_3_5 35 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 166 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 166 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 231 (accept_3_5 32 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 231 (accept_3_5 29 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 231 (accept_3_5 26 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 231
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 231 (accept_3_5 23 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 231 (accept_3_5 20 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 231 (accept_3_5 17 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 231 (accept_3_5 14 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 231 (accept_3_5 11 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 231 (accept_3_5 8 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 231 (accept_3_5 5 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 231 (Polychromatic418967fa.accept_22_4_12_11_1_13851 4 166 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 231 (accept_3_5 2 166 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 165 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 165 231 33 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 165 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 165 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 231 3 21 55 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 165 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 231 3 20 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 165 231 3 19 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 165 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 165 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 231 11 5 15 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 165 231 3 18 55 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 231 3 17 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 165 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 231 3 16 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 165 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 231 3 15 55 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 165 231 11 4 15 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 165 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 231 3 14 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 165 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 231 (Polychromatic418967fa.accept_9_4_3_6_1_532
  40 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 231 3 13 55 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 231 3 12 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 165 231 33 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 165 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 165 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 231 3 10 55 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 231 3 9 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 165 231 3 8 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 165 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 165 231 11 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 165 231 3 7 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 231 3 6 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 165 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 231 3 5 55 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 231 3 4 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 165 231 11 1 15 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 165 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 165 231 3 3 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 231 3 2 55 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 231 3 1 55 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 164 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 231 (accept_3_4 67 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 164 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 164 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 164 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 164 231 (accept_3_4 64 164 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 164 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 63 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 164 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 164 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 164 231 (accept_3_4 61 164 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 164 231 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 164 231 (accept_3_4 58 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 164 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 56 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 164 231 (accept_3_4 55 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 164 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 164 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 164 231 (accept_3_4 52 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 164 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 164 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 231 (accept_3_4 49 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 164 231 (accept_3_4 46 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 164 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 164 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 231 (accept_3_4 43 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 164 231 (accept_3_4 40 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 164 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 38 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 231 (accept_3_4 37 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 231 (Polychromatic418967fa.accept_19_17_12_3_1_12555 36
  164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 164 231 (accept_3_4 34 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 164 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 164 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 231 (accept_3_4 31 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 231 (accept_3_4 28 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 231 (accept_3_4 25 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 164 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 231 (accept_3_4 22 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 231 (accept_3_4 19 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 164 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 231 (accept_3_4 16 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 231 (accept_3_4 13 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 231 (accept_3_4 10 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 231 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 231 (accept_3_4 7 164 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 231 (accept_3_4 4 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 164 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 231 (accept_3_4 1 164 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 164 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 69 163 231 (Eq.refl Bool.true) (allA_succ_of_accept 68 163 231 (accept_3_5 68 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 163 231 (accept_3_5 65 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 163 231 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 231 (accept_3_5 62 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 231 (accept_3_5 59 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 231 (accept_3_5 56 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 231 (Polychromatic418967fa.accept_13_3_7_10_1_668 55 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 231
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 231 (accept_3_5 53 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 231 (accept_3_5 50 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 231 (accept_3_5 47 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 231 (accept_3_5 44 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 231
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 231 (accept_3_5 41 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 231 (accept_3_5 38 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 231 (Polychromatic418967fa.accept_15_7_13_6_1_696 37 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 231 (accept_3_5 35 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 231 (accept_3_5 32 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 231 (accept_3_5 29 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 231 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 231 (accept_3_5 26 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 231
  (Polychromatic418967fa.accept_22_2_9_11_1_13850 24 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 163 231 (accept_3_5 23 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 163 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 231 (accept_3_5 20 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 231 (Polychromatic418967fa.accept_14_5_9_7_1_590
  19 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 231
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 231 (accept_3_5 17 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 231 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 231 (accept_3_5 14 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 163 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 231 (accept_3_5 11 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 231 (accept_3_5 8 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 231
  (Polychromatic418967fa.accept_22_6_9_11_1_13849 6 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 231 (accept_3_5 5 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 231 (accept_3_5 2 163 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 231 (Polychromatic418967fa.accept_19_1_11_3_1_5463 1 163 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 162 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 162 231 3 23 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 162 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 231
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 67 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 231 3 22 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 162 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  64 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 162 231 3 21 54 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 162 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 162 231 3 20 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 162 231 (Polychromatic418967fa.accept_10_9_2_1_1_840
  59 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 162 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 162 231 3 19 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 162 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 231
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 231 3 18 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  52 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 162 231 3 17 54 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 162 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 231 3 16 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063
  47 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 162 231 3 15 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 162 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 231 (Polychromatic418967fa.accept_10_3_2_1_1_839
  43 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 231 3 14 54 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 162 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 162 231 3 13 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 162 231 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 231 3 12 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 231 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 162 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 162 231 3 11 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 162 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 231
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 231 3 10 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 162 231 3 9 54 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 162 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 231 3 8 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 231 (Polychromatic418967fa.accept_10_3_2_1_1_839
  23 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 162 231 3 7 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 162 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 162
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 231 3 6 54 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 231 3 5 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 231 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 231 3 4 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 231 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 162
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 231 3 3 54 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 231 3 2 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 162 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 162 231 3 1 54 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 162 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 162 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 161 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 161 231 7 10 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 161 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 161 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 231 (accept_3_4 67
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 161 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 231 (accept_3_4 64 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 161 231 7 9 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 161 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 231 (accept_3_4 61 161 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 161
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 231 (accept_3_4 58 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 161 231 7 8 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 161 231 (accept_3_4 55 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 231 (Polychromatic418967fa.accept_17_2_8_10_1_2870 53 161
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 231 (accept_3_4 52 161
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 231
  (Polychromatic418967fa.accept_19_13_9_3_1_9806 51 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 161 231 7 7 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 161 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 231 (accept_3_4 46 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 231 (accept_3_4 43 161 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 161 231 7 6 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 161 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 231 (accept_3_4 40 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 231 (accept_3_4 37 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 231 (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 161 231 7 5 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 161 231 (accept_3_4 34 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 161 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 231 (accept_3_4 31 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 161 231 7 4 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 161 231 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 161 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 231 (accept_3_4 25
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 231
  (Polychromatic418967fa.accept_15_9_11_6_1_637 24 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 161 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 231 (accept_3_4 22 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 161 231 7 3 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 161 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 231 (accept_3_4 19 161 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 231
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 231 (accept_3_4 16 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 161 231 7 2 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 161 231 (accept_3_4 13 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 161 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 231 (accept_3_4 10 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 161 231 7 1 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 231 (accept_3_4 4 161 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 231 (accept_3_4 1 161 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 160 231 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 160 231 (accept_3_5 71 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 160 231 (Polychromatic418967fa.accept_13_5_4_10_1_1244 70 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 160 231 (Polychromatic418967fa.accept_14_13_6_7_1_2013 69 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 160 231 (accept_3_5 68 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 160 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 160 231 (accept_3_5 65 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 160 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 160 231 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 231 (accept_3_5 62 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 160 231
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 160 231 (accept_3_5 59 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 160 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 160 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 160 231 (accept_3_5 56 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 160 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 160 231 (accept_3_5 53 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 160 231 (Polychromatic418967fa.accept_17_1_7_10_1_1835 52 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 160 231 (Polychromatic418967fa.accept_19_13_8_3_1_2906 51 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 160 231 (accept_3_5 50 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 160 231 (accept_3_5 47 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 160 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 160 231 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 231 (accept_3_5 44 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 231 (accept_3_5 41 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 231 (accept_3_5 38 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 231
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 231 (accept_3_5 35 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 231 (Polychromatic418967fa.accept_13_8_4_10_1_4358 34 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 231 (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 231 (accept_3_5 32 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 231 (accept_3_5 29 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 231 (accept_3_5 26 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 231
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 160 231 (accept_3_5 23 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 160 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 160 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 231 (accept_3_5 20 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 231 (accept_3_5 17 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 231 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 231 (accept_3_5 14 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 231 (accept_3_5 11 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 231 (Polychromatic418967fa.accept_18_9_16_15_1_2241 9 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 231 (accept_3_5 8 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 231 (accept_3_5 5 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 160 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 231 (accept_3_5 2 160 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 159 231 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 159 231 3 24 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 159 231 (Polychromatic418967fa.accept_13_6_3_10_1_698 71 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 231
  (Polychromatic418967fa.accept_16_6_15_7_1_1510 70 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 159 231 3 23 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 159 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 159 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 231 (Polychromatic418967fa.accept_13_2_3_10_1_658
  67 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 231 3 22 53 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 64 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 231 3 21 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 231 (Polychromatic418967fa.accept_10_2_9_1_1_185
  62 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 231
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 61 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 159 231 3 20 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 159 231 (Polychromatic418967fa.accept_13_7_3_10_1_656 59 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 58 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 231 3 19 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 231 (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 55 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 231 3 18 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 231 (Polychromatic418967fa.accept_19_15_7_3_1_4143 53 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 52 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 159 231 3 17 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 159 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 50 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 231
  (Polychromatic418967fa.accept_15_4_9_6_1_627 49 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 231 3 16 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 231 (Polychromatic418967fa.accept_25_22_9_6_1_13848 47 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 231
  (Polychromatic418967fa.accept_13_7_3_10_1_656 46 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 231 3 15 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 231 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 231
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 159 231 3 14 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 159 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 231
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 40 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 231 3 13 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 159 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 231
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 159 231 3 12 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 159 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 231
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 231 3 11 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 159 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323
  31 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 231 3 10 53 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 231
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 231 3 9 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 231 (Polychromatic418967fa.accept_14_12_5_7_1_2010
  26 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 231 3 8 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 231 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 159
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 231 3 7 53 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 231
  (Polychromatic418967fa.accept_13_7_3_10_1_656 20 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 231 (Polychromatic418967fa.accept_13_6_3_10_1_698 19 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 231 3 6 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 231
  (Polychromatic418967fa.accept_22_17_5_11_1_2772 17 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 159 231 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 231 3 5 53 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 231
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 231 (Polychromatic418967fa.accept_19_13_7_3_1_9798 13 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 231 3 4 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 231
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 159 231 (Polychromatic418967fa.accept_19_10_7_3_1_6977 10 159 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 231 3 3 53 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 231 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 231 3 2 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 159 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 231
  (Polychromatic418967fa.accept_15_4_9_6_1_627 4 159 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 231 3 1 53 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 159 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 159 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 158 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 231 (accept_3_4 73 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 158 231 (Polychromatic418967fa.accept_22_6_4_11_1_7374 72 158 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 158 231 (accept_3_4 70 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 158 231
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 68 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 158 231 (accept_3_4 67 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 158 231 (accept_3_4 64 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 158 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 158 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 158 231 (accept_3_4 61 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 158 231 (Polychromatic418967fa.accept_13_8_2_10_1_652 60 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 231 (accept_3_4 58 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 158 231 (accept_3_4 55 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 231 (accept_3_4 52 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 231 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 231
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 50 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 158 231 (accept_3_4 49 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 158 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 231 (accept_3_4 46 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 231 (accept_3_4 43 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 231 (accept_3_4 40 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 231 (accept_3_4 37 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 231 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 231 (accept_3_4 34 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 231
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 231 (accept_3_4 31 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 231 (accept_3_4 28 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 231 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 231 (accept_3_4 25 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 231 (accept_3_4 22 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 231 (accept_3_4 19 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 231 (accept_3_4 16 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 231 (Polychromatic418967fa.accept_16_15_14_7_1_10555 15 158 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 231
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 231 (accept_3_4 13 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 231 (accept_3_4 10 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 231 (accept_3_4 7 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 231 (accept_3_4 4 158 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 158 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 231 (accept_3_4 1 158 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 157 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 157 231 (accept_3_5 74 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 157 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 157 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 72 157
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 231 (accept_3_5 71 157
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 157 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 157 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 231 (accept_3_5 68 157 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 157 231 (Polychromatic418967fa.accept_14_11_3_7_1_604 67 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 231 (accept_3_5 65 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 231 (accept_3_5 62 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 157 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 231
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 231 (accept_3_5 59 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 231 (accept_3_5 56 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 231 (accept_3_5 53 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 231 (Polychromatic418967fa.accept_23_5_19_1_1_10609 51 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 231 (accept_3_5 50 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 231 (Polychromatic418967fa.accept_17_15_4_10_1_3968 49 157
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 231 (accept_3_5 47 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 231 (accept_3_5 44 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 157 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 231 (accept_3_5 41 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 231 (accept_3_5 38 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 231
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 231 (accept_3_5 35 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 231 (accept_3_5 32 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 231 (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 157
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 231 (accept_3_5 29 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 231 (accept_3_5 26 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 157 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 231 (accept_3_5 23 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 231 (accept_3_5 20 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 231 (accept_3_5 17 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 231 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 231 (accept_3_5 14 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 231 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 157
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 231 (accept_3_5 11 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 231 (accept_3_5 8 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 231 (accept_3_5 5 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 231 (accept_3_5 2 157 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 157 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 156 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 156 231 3 25 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 156 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 231 3 24 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 156 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  70 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 156 231 3 23 52 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 68 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 156 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 231 3 22 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 156 231 3 21 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 156 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  61 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 231 3 20 52 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 156 231 3 19 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 231 3 18 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 156 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  52 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 156 231 3 17 52 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 231 3 16 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 156 231 3 15 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 156 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 231 (Polychromatic418967fa.accept_8_3_4_7_1_475
  43 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 156 231 3 14 52 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 156 231 3 13 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 231 3 12 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 156 231 3 11 52 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 231 3 10 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 156 231 3 9 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 156 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 231 3 8 52 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 156 231 3 7 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 231 3 6 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 156 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 231 3 5 52 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 231 3 4 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 156 231 3 3 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 156 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 231 3 2 52 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 156 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 231 3 1 52 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 156 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 155 231
  (Eq.refl Bool.true) (allA_succ_of_accept 76 155 231 (accept_3_4 76 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 155 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 155 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 231 (accept_3_4 73 155 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 231
  (Polychromatic418967fa.accept_13_7_12_10_1_640 72 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 155 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 155 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 231 (accept_3_4 70 155 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 155 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 231 (accept_3_4 67 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 231 (Polychromatic418967fa.accept_20_5_15_11_1_3758 65 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 231 (accept_3_4 64 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63
  155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 231 (accept_3_4 61 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 231 (accept_3_4 58 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 231 (accept_3_4 55 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 231 (accept_3_4 52 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 231 (Polychromatic418967fa.accept_16_3_11_7_1_770 51 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 231 (accept_3_4 49 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 231 (accept_3_4 46 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 155
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 231 (accept_3_4 43 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 231 (accept_3_4 40 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 231 (accept_3_4 37 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 231 (accept_3_4 34 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 231 (accept_3_4 31 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 231 (accept_3_4 28 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 155
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 231 (accept_3_4 25 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 231 (accept_3_4 22 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 231 (accept_3_4 19 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 231 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 231 (accept_3_4 16 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 155 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 231 (accept_3_4 13 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 231 (accept_3_4 10 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 155 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 231 (accept_3_4 7 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 231 (accept_3_4 4 155 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 155 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 231 (accept_3_4 1 155 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 154 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 154 231 77 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 154 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 154 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 75
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 154 231 (accept_3_5 74
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 154 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 154 231 (Polychromatic418967fa.accept_25_22_4_6_1_10438 72 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 231 (accept_3_5 71 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 154 231 7 10 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 231 (accept_3_5 68 154 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 154 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 154 231 11 6 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 154 231 (accept_3_5 65
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 231
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 64 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 154 231 7 9 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 154 231 (accept_3_5 62 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 154
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 231 (accept_3_5 59 154
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 58 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 231 7 8 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 154 231 11 5 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 154 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 154 231 (accept_3_5 53 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 231 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 231 (accept_3_5 50 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 154 231 7 7 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 154 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 48
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 231 (accept_3_5 47
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 231
  (Polychromatic418967fa.accept_16_14_10_7_1_2363 46 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 231 11 4 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 231 7 6 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 154 231 (accept_3_5 41 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 154 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 154 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 231 (accept_3_5 38 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 231
  (Polychromatic418967fa.accept_19_17_2_3_1_4190 36 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 154 231 7 5 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 154 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 154 231 11 3 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 154 231 (accept_3_5 32 154 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 231 (accept_3_5 29 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  154 231 7 4 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 154 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 154 231 (accept_3_5 26 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 231 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 154
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 231 (accept_3_5 23 154
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 231 11 2 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 154 231 7 3 22 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 154 231 (accept_3_5 20 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 231 (accept_3_5 17 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 154 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 231 7 2 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 154 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 154 231 11 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 154 231 (Polychromatic418967fa.accept_15_10_4_6_1_2129
  10 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 231 (accept_3_5 8 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 154
  231 7 1 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  154 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 154 231 (accept_3_5 5 154 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 154 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 154 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 231 (accept_3_5 2 154 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  154 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 153 231 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 153 231 3 26 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 153 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 231
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 76 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 153 231 3 25 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370
  73 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 231 3 24 51 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 71 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 153 231 3 23 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 153 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  68 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 153 231 3 22 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 231
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 64 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 153 231 3 21 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 153 231 3 20 51 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 153 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 153 231 3 19 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 153 231 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  56 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 231 3 18 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 231 (Polychromatic418967fa.accept_10_2_3_1_1_481
  52 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 231 3 17 51 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 231 3 16 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 153 231 3 15 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 153 231 (Polychromatic418967fa.accept_19_6_1_3_1_11225 44 153 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 153 231 3 14 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 231
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 231 3 13 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 231 3 12 51 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 231 3 11 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 231 (Polychromatic418967fa.accept_10_2_3_1_1_481
  32 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 231 3 10 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  28 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 231 3 9 51 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 231 3 8 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 231 3 7 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 231 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 153
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 231 3 6 51 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 231 3 5 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 231 3 4 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 231 3 3 51 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 231
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 231 3 2 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 153 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 231
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 153 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 231 3 1 51 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 153 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 152 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 231 (accept_3_4 79 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 152 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 152 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 152 231 (accept_3_4 76 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 75
  152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 152 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 152 231 (accept_3_4 73 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 152 231 (Polychromatic418967fa.accept_14_2_12_7_1_617 72 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 152 231 (accept_3_4 70 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 152 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 152 231 (accept_3_4 67 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 231 (accept_3_4 64 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 152 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 231
  (Polychromatic418967fa.accept_25_12_2_6_1_13847 62 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 152 231 (accept_3_4 61 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 152 231 (Polychromatic418967fa.accept_16_12_8_7_1_4530 60 152 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 231 (accept_3_4 58 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 152 231 (accept_3_4 55 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 231 (accept_3_4 52 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 231 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 231 (accept_3_4 49 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 231 (accept_3_4 46 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 231
  (Polychromatic418967fa.accept_14_2_12_7_1_617 44 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 231 (accept_3_4 43 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 231 (accept_3_4 40 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 231 (accept_3_4 37 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 231 (accept_3_4 34 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 231 (accept_3_4 31 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 231 (accept_3_4 28 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 231 (accept_3_4 25 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 231 (Polychromatic418967fa.accept_17_7_16_10_1_1849 24 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 231 (accept_3_4 22 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 231 (accept_3_4 19 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 231 (accept_3_4 16 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 231 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 152 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 231 (accept_3_4 13 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 231 (accept_3_4 10 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 231
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 231 (accept_3_4 7 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 231 (accept_3_4 4 152 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 152 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 231 (accept_3_4 1 152 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 151 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 80 151 231 (accept_3_5 80 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 151 231 (Polychromatic418967fa.accept_22_13_19_11_1_9162 79 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 231 (Polychromatic418967fa.accept_15_3_1_6_1_206
  78 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 231 (accept_3_5 77
  151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 151 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 231 (accept_3_5 74 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 151 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 231
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 231 (accept_3_5 71 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 231 (accept_3_5 68 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 231 (accept_3_5 65 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 231 (accept_3_5 62 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 231 (Polychromatic418967fa.accept_19_4_18_3_1_5553 61 151
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 231
  (Polychromatic418967fa.accept_14_4_11_7_1_1234 60 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 231 (accept_3_5 59 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 231 (accept_3_5 56 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 231 (accept_3_5 53 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 231 (accept_3_5 50 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 231 (accept_3_5 47 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 231 (accept_3_5 44 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 43 151
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 231
  (Polychromatic418967fa.accept_17_8_15_10_1_10367 42 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 151 231 (accept_3_5 41 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 231 (accept_3_5 38 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 231
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 151 231 (accept_3_5 35 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 151
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 231 (accept_3_5 32 151
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 231
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 151 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 231 (accept_3_5 29 151 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 231
  (Polychromatic418967fa.accept_25_2_1_6_1_13846 27 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 231 (accept_3_5 26 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 231 (accept_3_5 23 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 231 (accept_3_5 20 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 231 (accept_3_5 17 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 231 (accept_3_5 14 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 231 (accept_3_5 11 151 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 231
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 231 (accept_3_5 8 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 231 (Polychromatic418967fa.accept_19_6_18_3_1_11230 6 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 231 (accept_3_5 5 151 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 231 (accept_3_5 2 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 151 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 150 231 (Eq.refl Bool.true) (allA_succ_of_gcd 81 150 231 3 27 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 150 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 150 231 (Polychromatic418967fa.accept_16_15_6_7_1_4512 79 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 231 3 26 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 76 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 150 231 3 25 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 74 150 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 231 3 24 50 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 231
  (Polychromatic418967fa.accept_18_17_6_15_1_8704 71 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 150 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 150 231 3 23 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 150 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 231 (Polychromatic418967fa.accept_14_11_10_7_1_1948 67 150 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 231 3 22 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 150 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 150 231 3 21 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331
  62 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 231 3 20 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 231 (Polychromatic418967fa.accept_14_3_10_7_1_3773 59 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 150 231 3 19 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 150 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 150 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 231 (Polychromatic418967fa.accept_13_3_7_10_1_668
  55 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 150 231 3 18 50 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 150 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 150 231 3 17 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331
  50 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 231 3 16 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 231 (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 150 231 3 15 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 150 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 150 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 231
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 231 3 14 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 231 (Polychromatic418967fa.accept_12_4_6_3_1_332
  40 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 150 231 3 13 50 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 231 3 12 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 231
  (Polychromatic418967fa.accept_17_1_14_10_1_10151 35 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 150 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 231 3 11 50 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 231 (Polychromatic418967fa.accept_14_3_10_7_1_3773 31 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 231 3 10 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 231 3 9 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 231 3 8 50 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 231
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 231 3 7 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 231 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 231
  (Polychromatic418967fa.accept_20_19_10_11_1_5107 19 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 150 231 3 6 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 150 231 3 5 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 231 3 4 50 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 231
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 150 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 150 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 150 231 3 3 50 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 150 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 231 (Polychromatic418967fa.accept_17_7_14_10_1_1846 7 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 231 3 2 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 150 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 150 231 3 1 50 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 150 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 150 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 149 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 149 231 (accept_3_4 82 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 149 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 149 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 149 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 231 (accept_3_4 79 149 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 231
  (Polychromatic418967fa.accept_13_12_6_10_1_667 77 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 231 (accept_3_4 76 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 231 (accept_3_4 73 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 231 (accept_3_4 70 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 231 (accept_3_4 67 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 231 (accept_3_4 64 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 231 (Polychromatic418967fa.accept_18_9_5_15_1_2246 63 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 231 (accept_3_4 61 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 231 (Polychromatic418967fa.accept_16_12_5_7_1_2360 60 149 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 231
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 59 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 231 (accept_3_4 58 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 231 (accept_3_4 55 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 231 (accept_3_4 52 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 231 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 231 (accept_3_4 49 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 231 (accept_3_4 46 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 231 (accept_3_4 43 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 231
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 231 (accept_3_4 40 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 231 (accept_3_4 37 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 231 (Polychromatic418967fa.accept_19_17_16_3_1_8401 36 149 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 231 (accept_3_4 34 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 231 (accept_3_4 31 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 231 (accept_3_4 28 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 231 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 231 (accept_3_4 25 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 231 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 149 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 231
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 231 (accept_3_4 22 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 231 (accept_3_4 19 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 231 (accept_3_4 16 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 231 (accept_3_4 13 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 231 (accept_3_4 10 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 231 (accept_3_4 7 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 231 (accept_3_4 4 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 149 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 231 (accept_3_4 1 149 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 148 231 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 231 (accept_3_5 83 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 148 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 148 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 148 231 (Polychromatic418967fa.accept_18_9_4_15_1_555 81 148
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 231 (accept_3_5 80 148
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 148 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 148 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 78 148 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 148 231 (accept_3_5 77 148 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 148 231 (Polychromatic418967fa.accept_14_6_8_7_1_589 76 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 148 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 75 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 148 231 (accept_3_5 74 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 148 231 (Polychromatic418967fa.accept_16_8_4_7_1_3390 72 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 148 231 (accept_3_5 71 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 148 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 148 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 148 231
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 148 231 (accept_3_5 68 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 148 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 148 231 (accept_3_5 65 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 148 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 148 231
  (Polychromatic418967fa.accept_10_3_8_1_1_182 63 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 148 231 (accept_3_5 62 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 148 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 148 231 (accept_3_5 59 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 148 231 (Polychromatic418967fa.accept_13_6_5_10_1_1213 58 148
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 148 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 148 231 (accept_3_5 56 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 148 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 148 231 (accept_3_5 53 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 148 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 148 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 148 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 148 231 (accept_3_5 50 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 148 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 148 231 (accept_3_5 47 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 148 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 231
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 148 231 (accept_3_5 44 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 148 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 231 (accept_3_5 41 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 148 231 (Polychromatic418967fa.accept_16_8_4_7_1_3390 40 148
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 148 231 (accept_3_5 38 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 148 231 (Polychromatic418967fa.accept_17_2_12_10_1_9034 36 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 231 (accept_3_5 35 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 148 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 148 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 231
  (Polychromatic418967fa.accept_10_3_8_1_1_182 33 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 231 (accept_3_5 32 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 231 (accept_3_5 29 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 231 (accept_3_5 26 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 231 (Polychromatic418967fa.accept_16_8_4_7_1_3390 24 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 231 (accept_3_5 23 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 231 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 148
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 231 (accept_3_5 20 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 231 (accept_3_5 17 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 148 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 231
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 231 (accept_3_5 14 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 231 (accept_3_5 11 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 231
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 231 (accept_3_5 8 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 231 (accept_3_5 5 148 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 231 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 148 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 231 (accept_3_5 2 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 147 231 (Eq.refl Bool.true) (allA_succ_of_gcd 84 147 231 21 4 7 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 147 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 83 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 231 3 27 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 80
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 147 231 3 26 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 147 231 7 11 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 147 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 147 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 147 231 3 25 49 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 147 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 74 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 147 231 3 24 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 147 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 71
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 147 231 7 10 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 147 231 3 23 49 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 147 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 68 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 147 231 3 22 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 147 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 231 21 3 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 147 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 147 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 231 3 20 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 231 3 19 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 147 231 7 8 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 231 3 18 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 231 3 17 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 147 231 7 7 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 147 231 3 16 49 77
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 147 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 147 231 3 15 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 147 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 44
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 231 21 2 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 147 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 147 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 231 3 13 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 231 3 12 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 147 231 7 5 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 147 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 231 3 11 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 231 3 10 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 231 7 4 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 147 231 3 9 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 231 3 8 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 231 21 1 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 231 3 6 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 231 3 5 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 147 231 7 2 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 231 3 4 49 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 231 3 3 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 231 7 1 21 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 147 231 3 2 49 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 231 3 1 49 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_231_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


