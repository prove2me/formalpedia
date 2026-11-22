-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch246
-- name    : Polychromatic418967fa_Branch246
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:02.804897+00:00
-- url     : https://prove2.me/theorems/1e19268b-5505-4feb-a65a-a36c24d08e3a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch246_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_246 : allB 246 246 :=
  allB_succ' 2 245 246 (Eq.refl Bool.true) (allA_succ_of_accept 1 245 246 (accept_3_4 1 245 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 246)) (allB_succ' 3 244 246 (Eq.refl Bool.true) (allA_succ_of_gcd 2 244 246 2 1 122
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 246
  (Polychromatic418967fa.accept_31_1_27_29_1_14812 1 244 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 244 246))) (allB_succ' 4 243 246 (Eq.refl Bool.true) (allA_succ_of_gcd 3 243 246 3 1 81 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 246
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 243 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 243 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 246)))) (allB_succ' 5 242 246 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  242 246 2 2 121 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 242 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 242 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 242 246 2 1 121 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 242 246 (accept_3_4 1 242 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 242 246))))) (allB_succ' 6 241 246 (Eq.refl Bool.true) (allA_succ_of_accept 5 241 246
  (accept_3_5 5 241 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 246
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 241 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 241 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 241 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 246 (accept_3_5 2 241 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 241 246 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 241 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 246)))))) (allB_succ' 7 240 246 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 240 246 6 1 40 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 240 246 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 240 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 246 2 2 120 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 240 246 3 1 80 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 240 246 2 1 120 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 240 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 246))))))) (allB_succ' 8 239 246 (Eq.refl Bool.true) (allA_succ_of_accept 7 239 246 (accept_3_4 7 239
  246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 239 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 239 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 239 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 246 (accept_3_4 4 239 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 239 246 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 239 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 2
  239 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 246 (accept_3_4 1 239
  246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239 246)))))))) (allB_succ' 9 238 246 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 238 246 2 4 119 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 238 246 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 238 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 238 246 2 3 119 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 238 246 (accept_3_5 5 238 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 238 246 2 2 119 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 238 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 3
  238 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 246 2 1 119 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 246
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 238 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 246))))))))) (allB_succ' 10 237 246 (Eq.refl Bool.true) (allA_succ_of_gcd 9 237 246 3 3 79 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 246
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 237 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 237 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 246 3 2 79 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 237 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 246
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 237 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 237 246 3 1 79 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 237 246 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 237 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 246 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 237 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 246)))))))))) (allB_succ' 11 236 246
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 236 246 2 5 118 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 246 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 236 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 246 2 4 118 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 246 (accept_3_4 7
  236 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 246 2 3 118 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 236 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 236 246 2 2 118 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 236 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 236 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 236 246 2 1 118 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 236 246 (accept_3_4 1 236 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 236 246))))))))))) (allB_succ' 12 235 246 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 235 246 (accept_3_5 11 235 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 235 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 235 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 246 (accept_3_5 8 235 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 246 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 235 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 246
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 235 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 246 (accept_3_5 5 235 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 246 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 235 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 235 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 246 (accept_3_5 2 235 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 235 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 246)))))))))))) (allB_succ' 13 234 246 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 234 246 6 2 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 234 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 246 2 5 117 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 234 246 3 3 78 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 246 2 4 117 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 246
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 234 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 246 6 1 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 234 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 246 2 2 117 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 246 3 1 78 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 246 2 1 117 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 246
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 234 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 246))))))))))))) (allB_succ' 14 233 246 (Eq.refl Bool.true) (allA_succ_of_accept 13 233 246 (accept_3_4
  13 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 246
  (Polychromatic418967fa.accept_22_12_13_4_1_10363 12 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 233 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 246 (accept_3_4 10 233 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 246 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 233 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 246
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 246 (accept_3_4 7 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 246 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 246 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 233 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 246 (accept_3_4 4 233 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 246
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 246 (accept_3_4 1 233 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  246)))))))))))))) (allB_succ' 15 232 246 (Eq.refl Bool.true) (allA_succ_of_gcd 14 232 246 2 7 116 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 246
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 232 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 246 2 6 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 232 246 (accept_3_5 11 232 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 232 246 2 5 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 232 246 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 232 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 246 2 4 116 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 246
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 232 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 246 2 3 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 246 (accept_3_5 5 232 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 246 2 2 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 246 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 232 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 246 2 1 116 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 246
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 232 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 246))))))))))))))) (allB_succ' 16 231 246 (Eq.refl Bool.true) (allA_succ_of_gcd 15 231 246 3 5 77 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 231 246
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 231 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 231 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 231 246 3 4 77 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 231 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  231 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 246
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 231 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 231 246 3 3 77 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 231 246 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 231 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 246 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 231 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 246 3 2 77 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 231 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 246 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 231 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 246 3 1 77 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 246 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 231 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 246
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 231 246)))))))))))))))) (allB_succ' 17 230 246 (Eq.refl Bool.true) (allA_succ_of_gcd 16 230 246 2 8 115 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 246
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 246 2 7 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 246 (accept_3_4 13 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 246 2 6 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 246 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 230 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 246 2 5 115 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 246
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 246 2 4 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 246 (accept_3_4 7 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 246 2 3 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 246 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 230 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 246 2 2 115 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 246
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 246 2 1 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 246 (accept_3_4 1 230 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  246))))))))))))))))) (allB_succ' 18 229 246 (Eq.refl Bool.true) (allA_succ_of_accept 17 229 246 (accept_3_5 17 229 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 246 (Polychromatic418967fa.accept_9_7_4_3_1_204
  16 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 246 (accept_3_5 14 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 246 (Polychromatic418967fa.accept_19_12_1_18_1_9570 12 229 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 246 (accept_3_5 11 229 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 246 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 229 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 246
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 246 (accept_3_5 8 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 246 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 229 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 246 (accept_3_5 5 229 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 246 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 229 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 246
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 246 (accept_3_5 2 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 246 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 229 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 246)))))))))))))))))) (allB_succ' 19 228 246 (Eq.refl Bool.true) (allA_succ_of_gcd 18 228
  246 6 3 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  228 246 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 228 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 228 246 2 8 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 246 3 5 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 246 2 7 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 246 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 228 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 246 6 2 38 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 246
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 228 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 228 246 2 5 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 228 246 3 3 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 246 2 4 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 246 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 228 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 246 6 1 38 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 246
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 228 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 228 246 2 2 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 228 246 3 1 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 228 246 2 1 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 228 246 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 228 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 246))))))))))))))))))) (allB_succ' 20 227 246
  (Eq.refl Bool.true) (allA_succ_of_accept 19 227 246 (accept_3_4 19 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 227 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 227 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 227 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 246 (accept_3_4 16 227 246
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 246 (Polychromatic418967fa.accept_9_6_2_3_1_771
  15 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 246
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 246 (accept_3_4 13 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 246 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 246 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 227 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 246 (accept_3_4 10 227 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 227 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 246
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 246 (accept_3_4 7 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 246 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 246 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 246 (accept_3_4 4 227 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 246 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 227 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 246
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 246 (accept_3_4 1 227 246 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  246)))))))))))))))))))) (allB_succ' 21 226 246 (Eq.refl Bool.true) (allA_succ_of_gcd 20 226 246 2 10 113 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 246
  (Polychromatic418967fa.accept_13_6_5_12_1_307 19 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 246 2 9 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 246 (accept_3_5 17 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 246 2 8 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 246 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 226 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 246 2 7 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 246
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 246 2 6 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 246 (accept_3_5 11 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 246 2 5 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 246 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 226 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 246 2 4 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 246
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 246 2 3 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 246 (accept_3_5 5 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 246 2 2 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 246 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 226 246 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 246 2 1 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 246
  (Polychromatic418967fa.accept_13_1_5_12_1_306 1 226 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 246))))))))))))))))))))) (allB_succ' 22 225 246 (Eq.refl Bool.true) (allA_succ_of_gcd 21 225 246 3 7 75
  82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 225 246
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 225 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 225 246 3 6 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 225 246
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 225 246 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 225 246 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 246 3 5 75 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 246
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 246 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 225 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 246 3 4 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 246
  (Polychromatic418967fa.accept_11_10_5_4_1_711 10 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 225 246 3 3 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 225 246 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 225 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 246 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 246 3 2 75 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 246
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 246 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 225 246 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 246 3 1 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 246 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 225 246
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 246
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 225 246 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 225 246)))))))))))))))))))))) (Polychromatic418967fa.branch_246_segment_002)))))))))))))))))))))


