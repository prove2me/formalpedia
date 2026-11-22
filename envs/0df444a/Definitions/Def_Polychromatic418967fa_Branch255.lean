-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch255
-- name    : Polychromatic418967fa_Branch255
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:30:06.868898+00:00
-- url     : https://prove2.me/theorems/9212f829-7963-4abc-ab94-6174873c6167
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch255_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_255 : allB 255 255 :=
  allB_succ' 2 254 255 (Eq.refl Bool.true) (allA_succ_of_accept 1 254 255 (accept_3_4 1 254 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 254 255)) (allB_succ' 3 253 255 (Eq.refl Bool.true) (allA_succ_of_accept 2 253 255
  (accept_3_5 2 253 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 253 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 1 253 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 253 255))) (allB_succ' 4 252 255 (Eq.refl Bool.true) (allA_succ_of_gcd 3 252 255 3 1 84 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 252 255
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 252 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 252 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 252 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 252 255)))) (allB_succ' 5 251 255 (Eq.refl Bool.true) (allA_succ_of_accept 4
  251 255 (accept_3_4 4 251 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 251 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 251 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 251 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 255 (accept_3_4 1 251 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 251 255))))) (allB_succ' 6 250 255 (Eq.refl Bool.true) (allA_succ_of_gcd 5 250 255 5 1 50 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 250 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 250 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 250 255 (Polychromatic418967fa.accept_20_3_10_15_1_620 3 250 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 255 (accept_3_5 2 250 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 250 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 250 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 255)))))) (allB_succ' 7 249 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 249 255 3 2 83 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 249 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 249 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 249 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 249 255 3 1 83 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 249 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 249 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 249 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 249 255))))))) (allB_succ' 8 248 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 248 255 (accept_3_4 7 248 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  248 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 248 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 248 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 248 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 255 (accept_3_4 4 248 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 248 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 248 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 248 255 (accept_3_4 1 248 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  255)))))))) (allB_succ' 9 247 255 (Eq.refl Bool.true) (allA_succ_of_accept 8 247 255 (accept_3_5 8 247 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 247 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 247 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 255 (accept_3_5 5 247 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 247 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 247 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 255 (accept_3_5 2 247 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 247 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 255))))))))) (allB_succ' 10 246 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 246 255 3 3 82 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 246 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 246 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 255 (Polychromatic418967fa.accept_13_7_12_8_1_199
  7 246 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 246 255 3 2 82 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 246 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 246 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 246 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 246 255 3 1 82 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 246 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 246 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 246 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 255)))))))))) (allB_succ' 11 245 255 (Eq.refl Bool.true) (allA_succ_of_gcd 10 245 255 5 2 49 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 245 255
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 245 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 245 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 255 (accept_3_4 7 245 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 245 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 245 255 5 1 49 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 245 255 (accept_3_4 4 245 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 245 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 245 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 255 (accept_3_4 1 245 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  255))))))))))) (allB_succ' 12 244 255 (Eq.refl Bool.true) (allA_succ_of_accept 11 244 255 (accept_3_5 11 244 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 244 255
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 244 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 244 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 244 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 244 255 (accept_3_5 8 244 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 244 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 244 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 244 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  244 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 244 255 (accept_3_5 5 244
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 244 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 244 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 244 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 255 (accept_3_5 2 244 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 244 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 244 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 255)))))))))))) (allB_succ' 13 243 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 243 255 3 4 81 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 243 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 243 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 243
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 243 255 3 3 81 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 243 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 243 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 243 255 3 2 81 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 243 255 (Polychromatic418967fa.accept_20_5_3_15_1_6909 5 243 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 243 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 243 255 3 1 81 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 243 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 243 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 243 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 255))))))))))))) (allB_succ' 14 242 255
  (Eq.refl Bool.true) (allA_succ_of_accept 13 242 255 (accept_3_4 13 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 242 255 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 242 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 242 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 242 255 (accept_3_4 10 242 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 242 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  242 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 242 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 242 255 (accept_3_4 7 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  242 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 242 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 242 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 255 (accept_3_4 4 242 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 242 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 255 (accept_3_4 1 242 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  255)))))))))))))) (allB_succ' 15 241 255 (Eq.refl Bool.true) (allA_succ_of_accept 14 241 255 (accept_3_5 14 241 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  241 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 255 (accept_3_5 11 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 241 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 255 (accept_3_5 8 241 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 255 (Polychromatic418967fa.accept_20_7_1_15_1_2700 7 241 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 255 (accept_3_5 5 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 241 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 241 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 255 (accept_3_5 2 241 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 241 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 255))))))))))))))) (allB_succ' 16 240 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 240 255 15 1 16 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 240 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 240 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 240 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 255 3 4 80 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 240 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 240 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 255 5 2 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 240 255 3 3 80 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 240 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  240 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 240 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 255 3 2 80 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 240 255 5 1 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 240 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 240 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 240 255 3 1 80 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 240 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 240 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 240 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 255)))))))))))))))) (allB_succ' 17 239 255 (Eq.refl Bool.true) (allA_succ_of_accept 16 239 255
  (accept_3_4 16 239 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 239 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 239 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 255 (accept_3_4 13 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 239 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 239 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  11 239 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 255 (accept_3_4 10
  239 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 239 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 239 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 255 (accept_3_4 7 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 239 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 239 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  239 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 255 (accept_3_4 4 239
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 239 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 239 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 255 (accept_3_4 1 239 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 239 255))))))))))))))))) (allB_succ' 18 238 255 (Eq.refl Bool.true) (allA_succ_of_gcd 17 238 255
  17 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 238
  255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 238 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 238 255 (accept_3_5 14 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 238 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 238 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 238 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 238 255 (accept_3_5 11 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 238 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 238 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 238 255 (accept_3_5 8 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 238 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 238 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 238 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 238 255 (accept_3_5 5 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  238 255 (Polychromatic418967fa.accept_16_4_14_15_1_6331 4 238 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 238 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 255 (accept_3_5 2 238 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 238 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 255)))))))))))))))))) (allB_succ' 19 237 255
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 237 255 3 6 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 237 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 237 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 237 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 237 255 3 5 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 237 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 237 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 237
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 237 255 3 4 79 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 237 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 237 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 237 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 237 255 3 3 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 237 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 237 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 237 255 3 2 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 237 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 237 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 237 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 237 255 3 1 79 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 237 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 237 255))))))))))))))))))) (allB_succ' 20 236 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 236 255 (accept_3_4 19 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 236 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 236 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 236 255 (accept_3_4 16 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 236 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 236 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 236 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 236 255 (accept_3_4 13 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 236 255 (Polychromatic418967fa.accept_18_12_2_3_1_6414 12 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 236 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 236 255 (accept_3_4 10 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 236 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 236 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 236 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 236 255 (accept_3_4 7 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  236 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 236 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 255 (accept_3_4 4 236 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 236 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 236 255 (accept_3_4 1 236 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  255)))))))))))))))))))) (allB_succ' 21 235 255 (Eq.refl Bool.true) (allA_succ_of_gcd 20 235 255 5 4 47 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 235 255
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 235 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 235 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 255 (accept_3_5 17 235 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 235 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 235 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 235 255 5 3 47 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 235 255 (accept_3_5 14 235 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 235 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 255 (accept_3_5 11 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  235 255 5 2 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 235 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 235 255 (accept_3_5 8 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 235 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 235 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 235 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 235 255 5 1 47 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 235 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 235 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 235 255 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 235 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 255 (accept_3_5 2 235 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 235 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 235 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 255))))))))))))))))))))) (allB_succ' 22 234 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 234 255 3 7 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 234 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 234 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 255 (Polychromatic418967fa.accept_10_9_4_5_1_616
  19 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 234 255 3 6 78 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 234 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 234 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 234 255 3 5 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 234 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 255 3 4 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 234 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 234 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 234
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 234 255 3 3 78 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 234 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 234 255 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 234 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 255 3 2 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 234 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 234 255 3 1 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 234 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 234 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234 255)))))))))))))))))))))) (allB_succ' 23
  233 255 (Eq.refl Bool.true) (allA_succ_of_accept 22 233 255 (accept_3_4 22 233 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 233 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 233 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 233 255 (accept_3_4 19 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 233 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 233 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 255 (accept_3_4 16 233 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 233 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 255 (accept_3_4 13 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 233 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 255 (accept_3_4 10 233 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 233 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 255 (accept_3_4 7 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 233 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 255 (accept_3_4 4 233 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 255 (Polychromatic418967fa.accept_19_3_5_8_1_8790 3 233 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 255 (accept_3_4 1 233 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  255))))))))))))))))))))))) (allB_succ' 24 232 255 (Eq.refl Bool.true) (allA_succ_of_accept 23 232 255 (accept_3_5 23
  232 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 232 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 232 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 232 255 (accept_3_5 20 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 232 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 232 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 232 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 232 255 (accept_3_5 17
  232 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 232 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 232 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 232 255 (accept_3_5 14 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 232 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 232 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 232 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 232 255 (accept_3_5 11
  232 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 10 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 232 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 255 (accept_3_5 8 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 232 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 232 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6
  232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 255 (accept_3_5 5 232
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 232 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 232 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 255 (accept_3_5 2 232 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 232 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 232 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 255)))))))))))))))))))))))) (allB_succ' 25 231 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 231 255 3 8 77 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 231 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 231 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  22 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 231 255 3 7 77 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 231 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 231 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 231 255 3 6 77 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 231 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 231 255 3 5 77 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 231 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 231 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 231 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 231 255 3 4 77 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 231 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 231 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 231 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 255 3 3 77 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 231 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 231 255 3 2 77 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 231 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 231 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 231 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 255 3 1 77 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 231 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 231 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 255))))))))))))))))))))))))) (allB_succ' 26 230 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 230 255 5 5 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 230 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 230 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 230 255 (accept_3_4 22 230 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 230 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  230 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 255 5 4 46 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 255 (accept_3_4 19
  230 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 230 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 230 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 230 255 (accept_3_4 16 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 230 255 5 3 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 230 255 (Polychromatic418967fa.accept_13_1_9_8_1_1734 14 230 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 255 (accept_3_4 13 230 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 230
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 230 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 255 5 2 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 230 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 230 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 255 (accept_3_4 7 230 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6
  230 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 230 255 5 1 46 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 230 255 (accept_3_4 4
  230 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 255
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 230 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 230 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 255 (accept_3_4 1 230 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 230 255)))))))))))))))))))))))))) (allB_succ' 27 229 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 229 255 (accept_3_5 26 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 255 (accept_3_5 23 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 229 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 255 (accept_3_5 20 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 255 (accept_3_5 17 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 229 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 255 (accept_3_5 14 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 255 (Polychromatic418967fa.accept_19_13_1_8_1_3281 13 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 255 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 229 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 255 (accept_3_5 11 229 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 255 (accept_3_5 8 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 255 (accept_3_5 5 229 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 229 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 255
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 3 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 255 (accept_3_5 2 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 229 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 255))))))))))))))))))))))))))) (allB_succ' 28 228 255 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 228 255 3 9 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 228 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 228
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 255 3 8 76 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 228 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 228 255 3 7 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 228 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 255 3 6 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 228
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 228 255 3 5 76 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 228 255
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 255 3 4 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 255
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 228 255 3 3 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 228 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 228 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 255 3 2 76 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 255 (Polychromatic418967fa.accept_21_4_18_3_1_11175 4 228 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 228 255 3 1 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 228 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 228 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 255)))))))))))))))))))))))))))) (allB_succ' 29 227 255 (Eq.refl Bool.true) (allA_succ_of_accept 28 227
  255 (accept_3_4 28 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 227 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 227 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 255 (accept_3_4 25 227 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 227 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 255 (Polychromatic418967fa.accept_9_5_2_3_1_194
  23 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 255 (accept_3_4 22
  227 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 227 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 227 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 255 (accept_3_4 19 227 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 227 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 227 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 255 (accept_3_4 16 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 255 (accept_3_4 13 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 227 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 255
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 255 (accept_3_4 10 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 255 (accept_3_4 7 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 227 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 255 (accept_3_4 4 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 227 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 255 (accept_3_4 1 227 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 255))))))))))))))))))))))))))))) (allB_succ' 30 226 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 226 255 (accept_3_5 29 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 226 255 (Polychromatic418967fa.accept_16_12_2_15_1_490 28 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 226 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 226 255 (accept_3_5 26 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 226 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 226 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 226 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 226 255 (accept_3_5 23 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 255 (accept_3_5 20 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 226 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 226 255 (accept_3_5 17 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 255 (accept_3_5 14 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 255 (accept_3_5 11 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 255 (accept_3_5 8 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 226 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 255 (accept_3_5 5 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 226 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 255 (accept_3_5 2 226 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 255)))))))))))))))))))))))))))))) (allB_succ' 31 225
  255 (Eq.refl Bool.true) (allA_succ_of_gcd 30 225 255 15 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 225 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 255
  (Polychromatic418967fa.accept_19_9_16_8_1_2097 28 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 225 255 3 9 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 225 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 225 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 225 255 5 5 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 225 255 3 8 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 225 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23
  225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 225 255 3 7 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 225 255 5 4 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 225 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 225 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 225 255 3 6 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 225 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 225 255 15 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 225 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  13 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 255 3 4 75 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 225 255 5 2 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 225 255 3 3 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 225 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 225 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 225 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 255 3 2 75 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 225 255 5 1 45 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 225 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 255 3 1 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 225 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 255)))))))))))))))))))))))))))))))
  (allB_succ' 32 224 255 (Eq.refl Bool.true) (allA_succ_of_accept 31 224 255 (accept_3_4 31 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 224 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 224 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 224 255 (accept_3_4 28 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 224 255 (Polychromatic418967fa.accept_18_9_8_3_1_2702 27 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 224 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 255 (accept_3_4 25 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 224 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 224 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 224 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 224 255 (accept_3_4 22 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 224 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 224 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 255 (accept_3_4 19 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 224 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 224 255 (accept_3_4 16 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 224 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 224 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 255 (accept_3_4 13 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 224 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 224 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 224 255 (accept_3_4 10 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  224 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 224 255 (Polychromatic418967fa.accept_21_8_14_3_1_9602 8 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 255 (accept_3_4 7 224 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 224 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 224 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 224 255 (accept_3_4 4 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  224 255 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 224 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 224 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 255 (accept_3_4 1 224 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 255)))))))))))))))))))))))))))))))) (allB_succ' 33 223 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 223 255 (accept_3_5 32 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 255 (accept_3_5 29 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 255 (accept_3_5 26 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 255 (accept_3_5 23 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 255 (accept_3_5 20 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 255 (accept_3_5 17 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 255 (accept_3_5 14 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 255 (accept_3_5 11 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 223 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 255 (accept_3_5 8 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 255 (accept_3_5 5 223 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 255
  (Polychromatic418967fa.accept_19_3_14_8_1_3272 3 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 255 (accept_3_5 2 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 223 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 255))))))))))))))))))))))))))))))))) (allB_succ' 34 222 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 222 255 3 11 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 222 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 222 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 222 255 3 10 74 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 222 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 222 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 222 255 3 9 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 222 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 255 3 8 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 222 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 222 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 222 255 3 7 74 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 222 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 222 255 3 6 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 222 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 222 255 3 5 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 222 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 222 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 255 3 4 74 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 222 255 3 3 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 222 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 222 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 255 3 2 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 222 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 255 3 1 74 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 222 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 222 255)))))))))))))))))))))))))))))))))) (allB_succ' 35 221 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 221 255 17 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 221 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 221 255 (accept_3_4 31 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 221 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 221 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 255 (accept_3_4 28 221 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 255 (accept_3_4 25 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 255 (Polychromatic418967fa.accept_19_4_12_8_1_10123 23 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 255 (accept_3_4 22 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 221
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 255 (accept_3_4 19 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 221 255 17 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 221 255 (accept_3_4 16 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 221 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 221 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 255 (accept_3_4 13 221 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 255
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 221 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 255 (accept_3_4 10 221 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 255 (accept_3_4 7 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 255 (Polychromatic418967fa.accept_19_5_12_8_1_7273 5 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 255 (accept_3_4 4 221 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 221 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 255 (accept_3_4 1 221 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  255))))))))))))))))))))))))))))))))))) (allB_succ' 36 220 255 (Eq.refl Bool.true) (allA_succ_of_gcd 35 220 255 5 7 44
  51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 220 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 220 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 220 255 (accept_3_5 32 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 220 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 220 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 255 5 6 44 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 255 (accept_3_5 29 220 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 220 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 220 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 255 (accept_3_5 26 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  220 255 5 5 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 220 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 220 255 (accept_3_5 23 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 220 255 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 255 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 220
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 255 5 4 44 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 220 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 255 (accept_3_5 17 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 220 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 220 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 220 255 5 3 44 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 220 255 (accept_3_5 14 220 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 220 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 255
  (Polychromatic418967fa.accept_19_12_11_8_1_2091 12 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 220 255 (accept_3_5 11 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 255 5 2 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 220 255 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 255 (accept_3_5 8 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 220 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 220 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 220 255 5 1 44 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 220 255
  (Polychromatic418967fa.accept_13_4_12_8_1_197 4 220 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 220 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 255 (accept_3_5 2 220 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 220 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 220 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 255)))))))))))))))))))))))))))))))))))) (allB_succ' 37 219 255
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 219 255 3 12 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 219 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 219
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 219 255 3 11 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 219 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 219 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 219 255 3 10 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 219 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 219 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 255 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 219 255 3 9 73 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 219 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 255 (Polychromatic418967fa.accept_20_5_19_15_1_3946 25 219 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 219 255 3 8 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 219 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 219 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 219 255 3 7 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 219 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 219 255 3 6 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 219 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 219 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 219
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 255 3 5 73 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 255
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 219 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 255 3 4 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 11
  219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 219 255 3 3 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 219 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 219 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 255
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 219 255 3 2 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 219 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 219 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 219 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 255 3 1 73 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 255
  (Polychromatic418967fa.accept_19_2_10_8_1_3218 2 219 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 219 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 255))))))))))))))))))))))))))))))))))))) (allB_succ' 38 218 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 255 (accept_3_4 37 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 218 255 (Polychromatic418967fa.accept_19_17_9_8_1_3269 36 218 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 218 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 255 (accept_3_4 34 218 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 255 (accept_3_4 31 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 255 (accept_3_4 28 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 218 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 218 255 (accept_3_4 25 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 218 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 218 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 255 (accept_3_4 22 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 218 255
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 218 255 (accept_3_4 19 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 218 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 255 (accept_3_4 16 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 218 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 255 (accept_3_4 13 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 255 (accept_3_4 10 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 255 (accept_3_4 7 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 255 (accept_3_4 4 218 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 218 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 255 (accept_3_4 1 218 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  255)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 217 255 (Eq.refl Bool.true) (allA_succ_of_accept 38 217 255
  (accept_3_5 38 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 217 255
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 217 255 (Polychromatic418967fa.accept_21_15_7_3_1_4886 36 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 255 (accept_3_5 35 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 255 (Polychromatic418967fa.accept_9_6_1_3_1_191
  33 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 255 (accept_3_5 32
  217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 255 (accept_3_5 29 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 217 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 255 (Polychromatic418967fa.accept_11_5_8_2_1_588
  27 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 255 (accept_3_5 26
  217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 217 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 255 (accept_3_5 23 217 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 255 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 255 (accept_3_5 20
  217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 255
  (Polychromatic418967fa.accept_20_19_17_15_1_2690 19 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 255 (accept_3_5 17 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 217 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 255 (accept_3_5 14 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 217 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 255 (accept_3_5 11 217 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 255 (accept_3_5 8 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 255 (accept_3_5 5 217 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 217 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 255 (accept_3_5 2 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 255 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 217 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 255))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 216 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 216 255 3 13 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 216 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 216 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 216 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 255 3 12 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 216 255 (Polychromatic418967fa.accept_19_16_7_8_1_8820 35 216 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 34 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 216 255 3 11 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 216 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 216 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 216 255 (Polychromatic418967fa.accept_10_1_6_5_1_304
  31 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 255 3 10 72 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 216 255 (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 216 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 216 255 3 9 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 216 255
  (Polychromatic418967fa.accept_21_5_6_3_1_12580 26 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 216 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 255 3 8 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 255
  (Polychromatic418967fa.accept_21_1_6_3_1_13982 22 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 216 255 3 7 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 216 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 216
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 255 3 6 72 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 255
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 216 255 3 5 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 216 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 255
  (Polychromatic418967fa.accept_21_13_6_3_1_3381 13 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 255 3 4 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 216
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 216 255 3 3 72 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 216 255
  (Polychromatic418967fa.accept_21_8_6_3_1_4881 8 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 216 255 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 255 3 2 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 255 (Polychromatic418967fa.accept_20_5_16_15_1_3957 5 216
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 216 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 216 255 3 1 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 216 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 216 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 216 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 255))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 215 255 (Eq.refl Bool.true) (allA_succ_of_gcd 40 215 255 5 8 43 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 215 255
  (Polychromatic418967fa.accept_21_18_5_3_1_11165 39 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 215 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 255 (accept_3_4 37 215 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 215 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 215 255 5 7 43 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 215 255 (accept_3_4 34 215 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 255 (Polychromatic418967fa.accept_9_6_8_3_1_183
  33 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 215 255 (accept_3_4 31 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  215 255 5 6 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 215 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 215 255 (accept_3_4 28 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 215 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 215 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 215 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 215 255 5 5 43 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 215 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 215 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 255 (accept_3_4 22 215 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 215 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 215 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 215 255 5 4 43 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 215 255 (accept_3_4 19 215 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 255
  (Polychromatic418967fa.accept_21_18_5_3_1_11165 18 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 215 255 (Polychromatic418967fa.accept_19_17_6_8_1_5928 17 215 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 255 (accept_3_4 16 215 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 215 255 5 3 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 215 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 255 (accept_3_4 13
  215 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 255
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 215 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 215 255 5 2 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 215 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9
  215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 255 (accept_3_4 7 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 215 255 5 1 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 215 255 (accept_3_4 4 215 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 215 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 215 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 215 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 255 (accept_3_4 1 215 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 255))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 214
  255 (Eq.refl Bool.true) (allA_succ_of_accept 41 214 255 (accept_3_5 41 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 214 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 214 255 (Polychromatic418967fa.accept_10_9_4_5_1_616
  39 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 255 (accept_3_5 38
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 214 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 214 255 (accept_3_5 35 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 214 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 214 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 255 (accept_3_5 32
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 214 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 214 255 (accept_3_5 29 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 214 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 214 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  27 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 255 (accept_3_5 26
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 214 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 214 255 (accept_3_5 23 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 214 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 214 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 255 (accept_3_5 20
  214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 214 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 214 255 (accept_3_5 17 214 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 214 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 214 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 214 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 214 255 (accept_3_5 14 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 214 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 214 255 (Polychromatic418967fa.accept_19_12_5_8_1_7294 12 214 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 214 255 (accept_3_5 11 214 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 214 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 214 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 214 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 255 (accept_3_5 8 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 255 (accept_3_5 5 214 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 214 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 255
  (Polychromatic418967fa.accept_19_3_5_8_1_8790 3 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 255 (accept_3_5 2 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 255)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 213 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 213 255 3 14 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 213 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 213 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 213 255 3 13 71 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 213 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 213 255 3 12 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 213 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 213 255 3 11 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 213 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 213 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 213 255 3 10 71 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 213 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 255 3 9 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 213 255 3 8 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 213 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 213 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 255 3 7 71 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 255 3 6 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 255 3 5 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 213 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 255 3 4 71 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 255 3 3 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 213 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 255 3 2 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 213 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 255 3 1 71 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 213 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 255))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 212 255
  (Eq.refl Bool.true) (allA_succ_of_accept 43 212 255 (accept_3_4 43 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 212 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 212 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 212 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 255 (accept_3_4 40 212 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 255
  (Polychromatic418967fa.accept_21_18_2_3_1_9685 39 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 212 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 212 255 (accept_3_4 37 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 212 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 255 (accept_3_4 34
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 212 255 (Polychromatic418967fa.accept_19_13_3_8_1_4534 32 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 212 255 (accept_3_4 31 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 212 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 255 (accept_3_4 28
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 212 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 255 (accept_3_4 25 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 212 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 212 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 255 (accept_3_4 22
  212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 255
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 212 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 255 (accept_3_4 19 212 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 212 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 212 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 212 255 (accept_3_4 16 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 212 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 212 255 (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 212 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 255 (accept_3_4 13 212 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 212 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 255 (accept_3_4 10 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 255 (accept_3_4 7 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 212 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 255 (accept_3_4 4 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 212 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 255 (accept_3_4 1 212 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 255)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 211 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 44 211 255 (accept_3_5 44 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 211 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 211 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 211 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 255 (accept_3_5 41 211 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40
  211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 211 255 (accept_3_5 38 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 211 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 211 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 255 (accept_3_5 35 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 211 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 255 (accept_3_5 32 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 255 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 255 (accept_3_5 29 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 211 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 255
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 211 255 (accept_3_5 26 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 211 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 211 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 211 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 255 (accept_3_5 23 211 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 255 (accept_3_5 20 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 255 (accept_3_5 17 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 211 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 255 (accept_3_5 14 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 255 (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 255 (accept_3_5 11 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 211 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 255 (accept_3_5 8 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 255 (accept_3_5 5 211 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 211 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 255
  (Polychromatic418967fa.accept_27_3_22_12_1_15555 3 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 211 255 (accept_3_5 2 211 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 211 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 211 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 211 255))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 210 255
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 210 255 15 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 210 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 210 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 255 3 14 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 210 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 210 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 255 5 8 42 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 210 255 3 13 70 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 210 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 210 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 255 3 12 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 210 255 5 7 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 210 255 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 210 255 3 11 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 210 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 210 255 (Polychromatic418967fa.accept_18_13_12_3_1_3857 31 210 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 210 255 15 2 14 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 210 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 210 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 210 255 3 9 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 210 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 210 255 5 5 42 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 210 255 3 8 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 255
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 210 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 210 255 3 7 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 255 5 4 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782
  19 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 255 3 6 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 210 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 210 255 15 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 210 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  14 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 255 3 4 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 255 (Polychromatic418967fa.accept_19_11_1_8_1_10127 11 210 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 255 5 2 42 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 255 3 3 70 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 210 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 255 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 255 3 2 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 210 255 5 1 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 210 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 210 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 210 255 3 1 70 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 210 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 210 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 210 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 255)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 209 255
  (Eq.refl Bool.true) (allA_succ_of_accept 46 209 255 (accept_3_4 46 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 209 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 209 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 209 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 255 (accept_3_4 43 209 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 255 (accept_3_4 40 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 255 (accept_3_4 37 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 209 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 255 (accept_3_4 34 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 255 (accept_3_4 31 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 209 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 255
  (Polychromatic418967fa.accept_25_4_9_5_1_10256 29 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 255 (accept_3_4 28 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 255 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 255 (accept_3_4 25 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 209 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 255 (accept_3_4 22 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 255 (accept_3_4 19 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 255 (accept_3_4 16 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 255 (accept_3_4 13 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 209 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 255 (accept_3_4 10 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 255 (accept_3_4 7 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 255 (accept_3_4 4 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 255 (Polychromatic418967fa.accept_20_3_9_15_1_6847 3 209 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 255 (accept_3_4 1 209 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 255))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 208 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 208 255 (accept_3_5 47 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 208 255 (Polychromatic418967fa.accept_22_2_10_13_1_10888 46 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 208 255 (Polychromatic418967fa.accept_11_1_10_2_1_58
  45 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 208 255 (accept_3_5 44
  208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 208 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 208 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 208 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 255 (accept_3_5 41 208 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 208 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 255
  (Polychromatic418967fa.accept_19_1_18_8_1_1066 39 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 255 (accept_3_5 38 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 255 (accept_3_5 35 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 208 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 255 (accept_3_5 32 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 255 (accept_3_5 29 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 255 (Polychromatic418967fa.accept_19_9_18_8_1_8782 28 208 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 255 (accept_3_5 26 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 255 (accept_3_5 23 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 208 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 255
  (Polychromatic418967fa.accept_22_21_10_13_1_13924 21 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 208 255 (accept_3_5 20 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 208 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 208
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 255 (accept_3_5 17 208
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 208 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 208 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 255 (accept_3_5 14 208 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 255 (accept_3_5 11
  208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 255
  (Polychromatic418967fa.accept_19_10_18_8_1_3238 10 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 208 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 255 (accept_3_5 8 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 208 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 255 (accept_3_5 5 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 208 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 255 (accept_3_5 2 208 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 255))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 207 255 (Eq.refl Bool.true) (allA_succ_of_gcd 48 207 255 3 16 69 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 207 255
  (Polychromatic418967fa.accept_19_9_17_8_1_2075 47 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 46 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 207 255 3 15 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 255 (Polychromatic418967fa.accept_13_5_12_8_1_198
  44 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 207 255 3 14 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 207 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 207 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 255 (Polychromatic418967fa.accept_11_7_9_2_1_260
  40 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 207 255 3 13 69 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 207 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 207 255 3 12 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 207 255 (Polychromatic418967fa.accept_13_9_12_8_1_570
  35 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 207 255 3 11 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 207 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 207 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 255 (Polychromatic418967fa.accept_13_5_12_8_1_198
  31 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 207 255 3 10 69 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 207 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 207 255 3 9 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207 255 (Polychromatic418967fa.accept_11_4_9_2_1_259
  26 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 255
  (Polychromatic418967fa.accept_18_7_9_3_1_800 25 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 207 255 3 8 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 207 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 207 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 255 3 7 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 19 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 255 3 6 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 255 (Polychromatic418967fa.accept_13_4_12_8_1_197
  17 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 255
  (Polychromatic418967fa.accept_19_16_17_8_1_8762 16 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 207 255 3 5 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 207 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 207 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 207 255 3 4 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 207 255 (Polychromatic418967fa.accept_19_11_17_8_1_7259 11 207 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 255
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 207 255 3 3 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 207 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 207 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 7
  207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 255 3 2 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 255
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 207 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 255 3 1 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 207 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 207 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 255))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 206 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 206 255 (accept_3_4 49 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 206 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 206 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 255 (accept_3_4 46 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 206 255 (accept_3_4 43 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 255 (accept_3_4 40 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 206 255 (accept_3_4 37 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 206 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 206 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 255 (accept_3_4 34 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 206 255 (accept_3_4 31 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 206 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 255 (accept_3_4 28 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 255
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 206 255 (accept_3_4 25 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 206 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 206 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 206 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 255 (accept_3_4 22 206 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 255 (accept_3_4 19 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 255 (accept_3_4 16 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 255 (accept_3_4 13 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 255 (accept_3_4 10 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 255
  (Polychromatic418967fa.accept_21_8_17_3_1_8031 8 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 255 (accept_3_4 7 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 255 (accept_3_4 4 206 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 206 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 255 (accept_3_4 1 206 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  255)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 205 255 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  205 255 5 10 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 205 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 255 (accept_3_5 47 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 205 255 5 9 41 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 205 255 (accept_3_5 44
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 205 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 255 (accept_3_5 41 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 205 255 5 8 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 205 255 (Polychromatic418967fa.accept_19_1_15_8_1_4538 39 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 255 (accept_3_5 38 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 205 255 5 7 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 205 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 255 (accept_3_5 32 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 205 255 5 6 41 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 205 255 (accept_3_5 29
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 205 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 255 (accept_3_5 26 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 205 255 5 5 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 205 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 255 (accept_3_5 23 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 205 255 5 4 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 205 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 255 (accept_3_5 17 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 205 255 5 3 41 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 205 255 (accept_3_5 14
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 205 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 255 (accept_3_5 11 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 205 255 5 2 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 205 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 255 (accept_3_5 8 205 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 205 255 5 1 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 205 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 205
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 255 (accept_3_5 2 205 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  205 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  255))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 204 255 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  204 255 51 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 204 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 204 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 204 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 204 255 3 16 68 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 204 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 204 255 3 15 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 204 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 255 3 14 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 204 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 204 255 3 13 68 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 204 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 255 3 12 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 35
  204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 255 17 2 12 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 204 255 3 11 68 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 204 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 204 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 255 3 10 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 204 255 3 9 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 204 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 204 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 255 3 8 68 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 204 255 3 7 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 204 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 255 3 6 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 17 204 255 17 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 204 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 204 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 204 255 3 5 68 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 204 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 255 3 4 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 204 255 3 3 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 204 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 204 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 255 3 2 68 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 204 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 204 255 3 1 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 204 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 204 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 255)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 203 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 203 255 (accept_3_4 52 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 255 (accept_3_4 49 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 255 (accept_3_4 46 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 255 (accept_3_4 43 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 255
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 255 (accept_3_4 40 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 255 (accept_3_4 37 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 255 (accept_3_4 34 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 255 (accept_3_4 31 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 255 (accept_3_4 28 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 255 (accept_3_4 25 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 255
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 203 255 (accept_3_4 22 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 203 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 203 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 203 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 255 (accept_3_4 19 203 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 255 (Polychromatic418967fa.accept_10_8_3_5_1_613
  18 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 255 (accept_3_4 16 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 255 (accept_3_4 13 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 255 (accept_3_4 10 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 255 (accept_3_4 7 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 203 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 255
  (Polychromatic418967fa.accept_19_5_13_8_1_3229 5 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 255 (accept_3_4 4 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 255 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 203 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 255 (accept_3_4 1 203 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 255))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 202 255
  (Eq.refl Bool.true) (allA_succ_of_accept 53 202 255 (accept_3_5 53 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 202 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 202 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 202 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 202 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 255 (accept_3_5 50 202 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 202 255 (accept_3_5 47 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 202 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 255 (accept_3_5 44 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 202 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 202 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 202 255 (accept_3_5 41 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 202 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796 40 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 202 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 255 (accept_3_5 38 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 202 255
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 202 255 (accept_3_5 35 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 202 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 255 (accept_3_5 32 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 255 (accept_3_5 29 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 255 (accept_3_5 26 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 255 (accept_3_5 23 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 255 (accept_3_5 20 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 255 (accept_3_5 17 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 255 (accept_3_5 14 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 255
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 255 (accept_3_5 11 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 255 (accept_3_5 8 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 255 (accept_3_5 5 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 202 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 255 (accept_3_5 2 202 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 201 255 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 201 255 3 18 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 201 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 255 (Polychromatic418967fa.accept_21_10_12_3_1_8076 52 201
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 201 255 3 17 67 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 201 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 201 255 3 16 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 201 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 201 255 3 15 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 201 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 201 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 201 255 3 14 67 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 201 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 201 255 3 13 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 201 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 201 255 3 12 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 201 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 201 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 201 255 3 11 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 201 255 (Polychromatic418967fa.accept_21_11_12_3_1_6461 32 201 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 201 255 3 10 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 201 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 201 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092
  28 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 255 3 9 67 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 255 3 8 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 201 255 3 7 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 201 255 (Polychromatic418967fa.accept_19_1_11_8_1_4504 20 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 201
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 255 3 6 67 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 255 3 5 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 201 255 3 4 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 201 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 255 3 3 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 255 3 2 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 201 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 201 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 201 255 3 1 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 201 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 201 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 200 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 200 255 5 11 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 200 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 200 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 255 (accept_3_4 52
  200 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 200 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 200 255 5 10 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 200 255 (accept_3_4 49 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 200 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 255 (accept_3_4 46 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 200 255 5 9 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 200 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 200 255 (accept_3_4 43 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 200 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 200 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 255 5 8 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 255
  (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 200 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 200 255 (accept_3_4 37 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 200 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 200 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 200 255 5 7 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 200 255 (accept_3_4 34 200 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 255 (accept_3_4 31 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  200 255 5 6 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 200 255 (accept_3_4 28 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 200 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 200 255 5 5 40 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 200 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 255 (accept_3_4 22 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 200 255 (Polychromatic418967fa.accept_14_7_4_3_1_488 21 200 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 255 5 4 40 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 255 (accept_3_4 19 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 200 255 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 200 255 (accept_3_4 16 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  200 255 5 3 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 200 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 200 255 (accept_3_4 13 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 200 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 200 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 255 5 2 40 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 255
  (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 200 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 255 (accept_3_4 7 200 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 200 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 200 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 200 255 5 1 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 200 255 (accept_3_4 4 200 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 200 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 255
  (Polychromatic418967fa.accept_19_2_10_8_1_3218 2 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 255 (accept_3_4 1 200 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 199 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 199 255 (accept_3_5 56 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 199 255 (Polychromatic418967fa.accept_19_17_9_8_1_3269 55 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 199 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 199 255 (accept_3_5 53 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 199 255 (accept_3_5 50 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 199 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 199 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 199 255 (accept_3_5 47 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 199 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 199 255 (accept_3_5 44 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 199 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 199 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 199 255 (accept_3_5 41 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 255
  (Polychromatic418967fa.accept_19_1_9_8_1_4474 39 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 199 255 (accept_3_5 38 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 199 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 199 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 255 (accept_3_5 35 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 199 255 (accept_3_5 32 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 199 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 199 255 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 255 (accept_3_5 29 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 199 255 (accept_3_5 26 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 199 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 199 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 255 (accept_3_5 23 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 255 (accept_3_5 20 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 255 (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 255 (accept_3_5 17 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 255 (accept_3_5 14 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 255 (accept_3_5 11 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 199 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 255 (accept_3_5 8 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 255 (accept_3_5 5 199 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 199 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 255
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 255 (accept_3_5 2 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 199 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 198 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 198 255 3 19 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 198 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 198 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 198 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 255 3 18 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 198 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  52 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 198 255 3 17 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 198 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 198 255 3 16 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 198 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 198 255 3 15 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 198 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 198 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 255 (Polychromatic418967fa.accept_7_1_2_3_1_257
  43 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 198 255 3 14 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 198 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 198 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 198 255 3 13 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 198 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 255 3 12 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 198 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  34 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 198 255 3 11 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 198 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 198 255 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 255 3 10 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 198 255 3 9 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 198 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 198 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 255 3 8 66 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 198 255 3 7 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 198 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 255 3 6 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 198
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 198 255 3 5 66 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 198 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 255 3 4 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 255 (Polychromatic418967fa.accept_13_11_3_8_1_1786
  11 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 198 255 3 3 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 198 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 198 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 255 3 2 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 198 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 255 3 1 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 198 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_255_segment_002)))))))))))))))))))))))))))))))))))))))))))))))))))))))))


