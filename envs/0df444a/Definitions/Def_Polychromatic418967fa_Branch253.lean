-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch253
-- name    : Polychromatic418967fa_Branch253
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:29.728308+00:00
-- url     : https://prove2.me/theorems/65a31e41-24e5-4c2f-9502-0f472b01a68f
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch253_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_253 : allB 253 253 :=
  allB_succ' 2 252 253 (Eq.refl Bool.true) (allA_succ_of_accept 1 252 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1
  252 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 253)) (allB_succ' 3 251 253
  (Eq.refl Bool.true) (allA_of_3_1 3 251 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 250 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 250 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 250 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 253 (accept_3_3 2 250 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 250 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 250 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 253)))) (allB_succ' 5 249 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 249 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 249 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 249 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 253 (accept_3_3 2 249 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1
  249 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 253))))) (allB_succ' 6 248 253
  (Eq.refl Bool.true) (allA_of_3_1 6 248 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 247 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 247 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 247 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 253 (accept_3_3 5 247 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 247 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 247 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 253 (accept_3_3 2 247 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 253 (Polychromatic418967fa.accept_17_1_9_15_1_3186 1 247 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 253))))))) (allB_succ' 8 246 253 (Eq.refl Bool.true) (allA_succ_of_accept 7 246 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 246 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 246 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 246 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 253 (accept_3_3 5 246 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 246 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 246 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 246 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  246 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 246 253 (accept_3_3 2 246
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 253
  (Polychromatic418967fa.accept_19_1_18_6_1_3110 1 246 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 253)))))))) (allB_succ' 9 245 253 (Eq.refl Bool.true) (allA_of_3_1 9 245 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 244 253 (Eq.refl Bool.true) (allA_succ_of_accept 9 244 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 244 253 (accept_3_3 8 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  244 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 244 253 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 244 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 244 253 (accept_3_3 5 244 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 253 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 244 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 244 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 244 253 (accept_3_3 2 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  244 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 244 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 244 253)))))))))) (allB_succ' 11 243 253 (Eq.refl Bool.true) (allA_succ_of_accept 10 243 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 243 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 243 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 243 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 253 (accept_3_3 8 243 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 243 253 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 243 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  243 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 253 (accept_3_3 5 243
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 253 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 243 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 243 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 253 (accept_3_3 2 243 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 243 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 253))))))))))) (allB_succ' 12 242 253 (Eq.refl Bool.true) (allA_of_3_1 12 242 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 241 253 (Eq.refl Bool.true) (allA_succ_of_accept 12 241 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 253 (accept_3_3 11 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 241 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 253 (accept_3_3 8 241 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 253 (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 241 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 253 (accept_3_3 5 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 241 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 241 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 253 (accept_3_3 2 241 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 241 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 253))))))))))))) (allB_succ' 14 240 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 240 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 240 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  240 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 240 253 (accept_3_3 11
  240 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 240 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 240 253 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 240 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 253 (accept_3_3 8 240 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 240 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 240 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  240 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 240 253 (accept_3_3 5 240
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 240 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 240 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 240 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 253 (accept_3_3 2 240 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 240 253 (Polychromatic418967fa.accept_26_1_6_19_1_15480 1 240 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 253)))))))))))))) (allB_succ' 15 239 253 (Eq.refl
  Bool.true) (allA_of_3_1 15 239 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 238 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 238 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 238 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 238 253 (accept_3_3 14 238 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 238 253 (Polychromatic418967fa.accept_19_13_10_6_1_7147 13 238 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 238 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 238 253 (accept_3_3 11 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 238 253 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 238 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 238 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 238 253 (accept_3_3 8 238 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 238 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 238 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 238 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 238 253 (accept_3_3 5 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  238 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 238 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 238 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 238 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 253 (accept_3_3 2 238 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 238 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 238 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 253)))))))))))))))) (allB_succ' 17 237 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 237 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 237 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 253 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 253 (accept_3_3 14
  237 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 237 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 237 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 253 (accept_3_3 11 237 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 237 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 237 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 253 (accept_3_3 8 237
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 237 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 237 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 253 (accept_3_3 5 237 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 237 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 253 (accept_3_3 2 237
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 253
  (Polychromatic418967fa.accept_13_1_3_6_1_158 1 237 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 237 253))))))))))))))))) (allB_succ' 18 236 253 (Eq.refl Bool.true) (allA_of_3_1 18 236 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 235 253 (Eq.refl Bool.true) (allA_succ_of_accept 18 235 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 235 253 (accept_3_3 17 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 235 253 (Polychromatic418967fa.accept_13_3_1_6_1_509 16 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 235 253 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 235 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 253 (accept_3_3 14 235 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 253 (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 235
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 253 (accept_3_3 11 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 253 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 235 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 253 (accept_3_3 8 235 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 235 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 253 (accept_3_3 5 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 253 (Polychromatic418967fa.accept_14_4_11_1_1_940 4 235 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 235 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 253 (accept_3_3 2 235 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 235 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 253))))))))))))))))))) (allB_succ' 20 234 253
  (Eq.refl Bool.true) (allA_succ_of_accept 19 234 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 234 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 234 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 234 253 (accept_3_3 17 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 234 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 234 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 234 253 (accept_3_3 14 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 253 (Polychromatic418967fa.accept_22_13_14_11_1_15479 13 234 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 234 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 234 253 (accept_3_3 11 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 234 253 (Polychromatic418967fa.accept_21_10_3_1_1_3323 10 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 234 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 253 (accept_3_3 8 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 234 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 253
  (Polychromatic418967fa.accept_21_6_3_1_1_6286 6 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 234 253 (accept_3_3 5 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  234 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 234 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 234 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 253 (accept_3_3 2 234 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 253 (Polychromatic418967fa.accept_20_1_14_13_1_6735 1 234 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234 253)))))))))))))))))))) (allB_succ' 21 233 253
  (Eq.refl Bool.true) (allA_of_3_1 21 233 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 232 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 232 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 232 253 (accept_3_3 20 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 232 253 (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 232 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 232 253
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 232 253 (accept_3_3 17 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 232 253 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 232 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 232 253 (accept_3_3 14 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 232 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 232 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 232 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 232 253 (accept_3_3 11 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 232 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 232 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 253 (accept_3_3 8 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 232 253 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 232 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 232 253 (accept_3_3 5 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  232 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 232 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 232 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 253 (accept_3_3 2 232 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 232 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 232 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 253)))))))))))))))))))))) (allB_succ' 23 231 253
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 231 253 11 2 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 231 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 231 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 253 (accept_3_3 20 231 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 253 (Polychromatic418967fa.accept_15_4_6_13_1_956
  19 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 231 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 231 253 (accept_3_3 17 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 231 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 231 253 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 231 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 253 (accept_3_3 14 231 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 231 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 231 253 11 1 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 231 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 231 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 253 (accept_3_3 8 231
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 253
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 231 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 253 (accept_3_3 5 231 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 231 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3
  231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 253 (accept_3_3 2 231
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 253
  (Polychromatic418967fa.accept_19_1_3_6_1_5827 1 231 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 231 253))))))))))))))))))))))) (allB_succ' 24 230 253 (Eq.refl Bool.true) (allA_of_3_1 24 230 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 229 253 (Eq.refl Bool.true) (allA_succ_of_accept 24 229 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 229 253 (accept_3_3 23 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 253 (Polychromatic418967fa.accept_19_3_1_6_1_3114 22 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 253 (accept_3_3 20 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 253 (Polychromatic418967fa.accept_20_19_9_13_1_2598 19 229 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 253 (accept_3_3 17 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 253 (accept_3_3 14 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 229 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 253 (accept_3_3 11 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 253 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 229 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 253 (accept_3_3 8 229 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 229 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 253 (accept_3_3 5 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 229 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 253 (accept_3_3 2 229 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 229 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 253))))))))))))))))))))))))) (allB_succ' 26 228 253
  (Eq.refl Bool.true) (allA_succ_of_accept 25 228 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 228 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 228 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 228 253 (accept_3_3 23 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 228 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 228 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 228 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 253 (accept_3_3 20 228 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 228 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 228 253
  (Polychromatic418967fa.accept_20_18_8_13_1_6761 18 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 228 253 (accept_3_3 17 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 228 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 228 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 228 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 253 (accept_3_3 14 228 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 253 (Polychromatic418967fa.accept_9_4_3_1_1_154
  13 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 228 253 (accept_3_3 11 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 228 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 228 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 228 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 253 (accept_3_3 8 228 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 228 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 228 253 (accept_3_3 5 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  228 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 228 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 228 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 228 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 253 (accept_3_3 2 228 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 228 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 253)))))))))))))))))))))))))) (allB_succ' 27 227 253
  (Eq.refl Bool.true) (allA_of_3_1 27 227 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 226 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 226 253 (accept_3_3 26 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 226 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 226 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 226 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 226 253 (accept_3_3 23 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 253 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 253 (accept_3_3 20 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 226 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 226 253 (accept_3_3 17 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 253 (accept_3_3 14 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 226 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 253
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 253 (accept_3_3 11 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 253 (accept_3_3 8 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 253 (accept_3_3 5 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 226 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 253 (accept_3_3 2 226 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 226 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 253)))))))))))))))))))))))))))) (allB_succ' 29 225
  253 (Eq.refl Bool.true) (allA_succ_of_accept 28 225 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 253
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 253 (accept_3_3 26 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 225 253 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 253 (accept_3_3 23 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 225 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 253
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 253 (accept_3_3 20 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 253 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 253 (accept_3_3 17 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 253 (accept_3_3 14 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 253 (Polychromatic418967fa.accept_22_13_5_11_1_15478 13 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 253 (accept_3_3 11 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 225 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 253
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 253 (accept_3_3 8 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 253 (Polychromatic418967fa.accept_18_6_9_1_1_3769 6 225 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 253 (accept_3_3 5 225 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 253 (accept_3_3 2 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 253 (Polychromatic418967fa.accept_24_1_9_13_1_13713 1 225 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 253))))))))))))))))))))))))))))) (allB_succ' 30 224 253 (Eq.refl Bool.true) (allA_of_3_1 30
  224 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 223 253 (Eq.refl Bool.true) (allA_succ_of_accept 30
  223 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 223 253 (accept_3_3 29 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 223 253 (Polychromatic418967fa.accept_16_12_15_13_1_3872 28 223 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 253 (Polychromatic418967fa.accept_13_1_2_6_1_515
  27 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 253 (accept_3_3 26
  223 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 223 253
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 223 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 253 (accept_3_3 23 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 223 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 223 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 253 (Polychromatic418967fa.accept_9_3_7_1_1_143
  21 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 253 (accept_3_3 20
  223 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 223 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 253 (accept_3_3 17 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 223 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 223 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 253 (Polychromatic418967fa.accept_9_6_7_1_1_145
  15 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 253 (accept_3_3 14
  223 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 253
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 223 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 253 (accept_3_3 11 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 223 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 253 (accept_3_3 8 223
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 253
  (Polychromatic418967fa.accept_14_7_13_1_1_922 7 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 223 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 253 (accept_3_3 5 223 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 223 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 223 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 253 (accept_3_3 2 223
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 253
  (Polychromatic418967fa.accept_13_1_2_6_1_515 1 223 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 223 253))))))))))))))))))))))))))))))) (allB_succ' 32 222 253 (Eq.refl Bool.true) (allA_succ_of_accept 31
  222 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 222 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 222 253 (accept_3_3 29 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 253 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 222 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 222 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 222 253 (accept_3_3 26 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 222 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 222 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 222 253 (accept_3_3 23 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 222 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 222 253 (accept_3_3 20 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 222 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 222 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 222 253 (accept_3_3 17 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 222 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 222 253 (accept_3_3 14 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 222 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 222 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 253 (accept_3_3 11 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 222 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 253
  (Polychromatic418967fa.accept_13_9_1_6_1_510 9 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 222 253 (accept_3_3 8 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  222 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 222 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 253 (accept_3_3 5 222 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 222 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 222 253 (accept_3_3 2 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  222 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 222 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 222 253)))))))))))))))))))))))))))))))) (allB_succ' 33 221 253 (Eq.refl Bool.true) (allA_of_3_1
  33 221 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 220 253 (Eq.refl Bool.true) (allA_succ_of_gcd 33
  220 253 11 3 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 220 253 (accept_3_3 32 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 220 253 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 220 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 220 253 (accept_3_3 29 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 220 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 220 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 253 (accept_3_3 26 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 220 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 220 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 220 253 (accept_3_3 23 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 253 11 2 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 220 253 (accept_3_3 20 220 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 220 253 (Polychromatic418967fa.accept_7_5_3_1_1_424
  19 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 220 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 220 253 (accept_3_3 17 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 220 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 220 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 220 253 (accept_3_3 14 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 253 (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 220 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 220 253 11 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 220 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 220 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 253 (accept_3_3 8 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 253 (accept_3_3 5 220 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 220 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 253 (accept_3_3 2 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 220 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 253)))))))))))))))))))))))))))))))))) (allB_succ' 35 219 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 219 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 219 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 219 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 253 (accept_3_3 32 219 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 253 (Polychromatic418967fa.accept_7_3_2_1_1_225
  31 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 253 (accept_3_3 29 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 253 (accept_3_3 26 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 253 (accept_3_3 23 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 253 (accept_3_3 20 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 253 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 219
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 253 (accept_3_3 17 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 219 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 253 (accept_3_3 14 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 253
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 219 253 (accept_3_3 11 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 219 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 219 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 253 (accept_3_3 8 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 219 253 (accept_3_3 5 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  219 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 219 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 253 (accept_3_3 2 219 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 253 (Polychromatic418967fa.accept_19_1_10_6_1_5726 1 219 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 253))))))))))))))))))))))))))))))))))) (allB_succ'
  36 218 253 (Eq.refl Bool.true) (allA_of_3_1 36 218 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 217 253
  (Eq.refl Bool.true) (allA_succ_of_accept 36 217 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 253 (accept_3_3 35 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 217 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 217 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 253
  (Polychromatic418967fa.accept_13_7_9_6_1_148 33 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 253 (accept_3_3 32 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 253 (Polychromatic418967fa.accept_19_12_8_6_1_8646 31 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 253 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 253 (accept_3_3 29 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 217 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 253
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 253 (accept_3_3 26 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 253 (accept_3_3 23 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 253 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 253
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 253 (accept_3_3 20 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 253 (Polychromatic418967fa.accept_17_2_13_15_1_4349 19 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 253 (Polychromatic418967fa.accept_27_18_1_10_1_11658 18 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 253 (accept_3_3 17 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 217
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 253
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 253 (accept_3_3 14 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 253 (accept_3_3 11 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 253 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 217 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 253
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 253 (accept_3_3 8 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 253 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 253 (accept_3_3 5 217 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 217 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 253
  (Polychromatic418967fa.accept_13_3_9_6_1_502 3 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 253 (accept_3_3 2 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 217 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 253))))))))))))))))))))))))))))))))))))) (allB_succ' 38 216 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 216 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 216 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 216 253 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 216
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 216 253 (accept_3_3 35 216
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 253
  (Polychromatic418967fa.accept_15_4_6_13_1_956 34 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 216 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 216 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 253 (accept_3_3 32 216 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 216 253 (Polychromatic418967fa.accept_17_14_12_15_1_5558 31 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 216 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 216 253 (accept_3_3 29 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 216 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 216 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 253 (accept_3_3 26 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 253 (Polychromatic418967fa.accept_31_25_30_5_1_15477 25
  216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 253
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 216 253 (accept_3_3 23 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 216 253 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 253 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 253 (accept_3_3 20 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 216 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 216 253 (accept_3_3 17 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 216 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 216 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 253 (accept_3_3 14 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 253 (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 216
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 216 253 (accept_3_3 11 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 216 253 (Polychromatic418967fa.accept_22_10_18_11_1_15425 10 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 253 (accept_3_3 8 216 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 216 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 253
  (Polychromatic418967fa.accept_22_6_18_11_1_13837 6 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 216 253 (accept_3_3 5 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 253 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 216 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 253 (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 216
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 253 (accept_3_3 2 216 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016
  1 216 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  253)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 215 253 (Eq.refl Bool.true) (allA_of_3_1 39 215 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 214 253 (Eq.refl Bool.true) (allA_succ_of_accept 39 214 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 214 253 (accept_3_3 38 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 214 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 214 253 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 214 253 (accept_3_3 35 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 214 253 (Polychromatic418967fa.accept_19_15_5_6_1_5760 34 214
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 214 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 214 253 (accept_3_3 32 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 214 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 214 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 214 253 (accept_3_3 29 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 214 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 214 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 214 253 (accept_3_3 26 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 214 253 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 214 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 214 253 (accept_3_3 23 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 214 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 214 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 214 253 (accept_3_3 20 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 214 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 214 253 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 214 253 (accept_3_3 17 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 214 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 214
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 214 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 214 253 (accept_3_3 14 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 214 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 214 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 214 253 (accept_3_3 11 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 214 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 214 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 253 (accept_3_3 8 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 253 (accept_3_3 5 214 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 214 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 253 (accept_3_3 2 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 253 (Polychromatic418967fa.accept_19_1_5_6_1_5811 1 214 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 253)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 213 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 213 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 213 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 253 (accept_3_3 38 213 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 253
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 213 253 (accept_3_3 35 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 213 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 253 (accept_3_3 32 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 213 253 (accept_3_3 29 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 213 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 253 (accept_3_3 26 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 213 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 253
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 213 253 (accept_3_3 23 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 213 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 253 (accept_3_3 20 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 213 253 (accept_3_3 17 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 213 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 253 (accept_3_3 14 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 213 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 253 (accept_3_3 11 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 253 (accept_3_3 8 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 253
  (Polychromatic418967fa.accept_17_6_9_15_1_3185 6 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 253 (accept_3_3 5 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 253 (accept_3_3 2 213 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 213 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 253)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 212 253 (Eq.refl Bool.true) (allA_of_3_1 42 212 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 211 253 (Eq.refl Bool.true) (allA_succ_of_accept 42 211 253 (Polychromatic418967fa.accept_4_2_3_1_1_2
  42 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 253 (accept_3_3 41
  211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 211 253
  (Polychromatic418967fa.accept_13_1_3_6_1_158 40 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 211 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 211 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 253 (accept_3_3 38 211 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 211 253 (Polychromatic418967fa.accept_25_12_11_3_1_15476 37 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 253
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 253 (accept_3_3 35 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 253 (accept_3_3 32 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 253 (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 253 (accept_3_3 29 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 253 (accept_3_3 26 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 211 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 253 (accept_3_3 23 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 253 (accept_3_3 20 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 253 (Polychromatic418967fa.accept_17_2_7_15_1_5525 19 211 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 253 (accept_3_3 17 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 253 (accept_3_3 14 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 253 (Polychromatic418967fa.accept_19_13_2_6_1_13962 13 211 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 253 (accept_3_3 11 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 253 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 253 (accept_3_3 8 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 253 (accept_3_3 5 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 253 (Polychromatic418967fa.accept_19_4_2_6_1_7181 4 211 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 253 (accept_3_3 2 211 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 211 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 253)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 210 253 (Eq.refl Bool.true) (allA_succ_of_accept 43 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50
  43 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 210 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 210 253 (accept_3_3 41 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 210 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 253 (accept_3_3 38 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 253 (Polychromatic418967fa.accept_16_5_2_13_1_1007 37 210 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 253
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 210 253 (accept_3_3 35 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 210 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 210 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 253 (accept_3_3 32 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 210 253
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 210 253 (accept_3_3 29 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 210 253 (Polychromatic418967fa.accept_29_28_7_21_1_15475 28 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 253 (accept_3_3 26 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 210 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 210 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 210 253 (accept_3_3 23 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 210 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 210 253 (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 253 (accept_3_3 20 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 253
  (Polychromatic418967fa.accept_19_18_1_6_1_5807 18 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 253 (accept_3_3 17 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 210 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 253 (accept_3_3 14 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 253
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 210 253 (accept_3_3 11 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 210 253 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 210 253 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 253 (accept_3_3 8 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 253 (accept_3_3 5 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  210 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 210 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 253 (accept_3_3 2 210 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 210 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 253))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 209 253 (Eq.refl Bool.true) (allA_of_3_1 45 209 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 208 253 (Eq.refl Bool.true) (allA_succ_of_accept 45 208 253 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 208 253 (accept_3_3 44
  208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 208 253
  (Polychromatic418967fa.accept_19_5_18_6_1_7191 43 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 208 253 (Polychromatic418967fa.accept_25_17_8_3_1_10038 42 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 253 (accept_3_3 41 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 253 (Polychromatic418967fa.accept_22_18_10_11_1_7381 40 208 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 253 (accept_3_3 38 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 253 (Polychromatic418967fa.accept_21_16_19_1_1_6320 37 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 253 (accept_3_3 35 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 208 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 253 (accept_3_3 32 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 253 (Polychromatic418967fa.accept_19_11_18_6_1_3113 30 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 253 (accept_3_3 29 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 253 (Polychromatic418967fa.accept_17_11_4_15_1_3150 28 208
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 253 (accept_3_3 26 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 253 (accept_3_3 23 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 208 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 253 (accept_3_3 20 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 253 (Polychromatic418967fa.accept_17_2_4_15_1_5451 19 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 253 (accept_3_3 17 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 253 (accept_3_3 14 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 208 253 (Polychromatic418967fa.accept_19_12_18_6_1_14021 12 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 253 (accept_3_3 11 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 208 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 253 (accept_3_3 8 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 253 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 253 (accept_3_3 5 208 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 208 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 253 (accept_3_3 2 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 208 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 253)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 207 253 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 207 253 23 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 207 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 207 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 253 (accept_3_3 44 207 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 207 253 (Polychromatic418967fa.accept_28_15_11_1_1_15457 43 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 253 (accept_3_3 41 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 253 (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 253 (accept_3_3 38 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 253 (Polychromatic418967fa.accept_19_18_17_6_1_5775 37 207
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 253
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 207 253 (accept_3_3 35 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 207 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 207 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 253 (accept_3_3 32 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 253 (accept_3_3 29 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 253 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 253 (accept_3_3 26 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 207
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 23 207 253 23 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 207 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 207
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 253 (accept_3_3 20 207
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 207 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 253 (accept_3_3 17 207 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 253 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 253 (accept_3_3 14
  207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 253
  (Polychromatic418967fa.accept_19_13_17_6_1_11363 13 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 253 (accept_3_3 11 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 253 (accept_3_3 8 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 253 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 253 (accept_3_3 5 207 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 253 (accept_3_3 2 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 207 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 253))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 206 253 (Eq.refl
  Bool.true) (allA_of_3_1 48 206 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 205 253 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 205 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 205 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 253 (accept_3_3 47 205 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 205 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 205 253 (accept_3_3 44 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 253 (Polychromatic418967fa.accept_13_4_10_6_1_989 43 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 253 (accept_3_3 41 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 253 (accept_3_3 38 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 205 253 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 253 (accept_3_3 35 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 205 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 253 (accept_3_3 32 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 253 (accept_3_3 29 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 253 (accept_3_3 26 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 205 253 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 205 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 253 (accept_3_3 23 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 253 (accept_3_3 20 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 253 (accept_3_3 17 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 253 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 205
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 253 (accept_3_3 14 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 253 (accept_3_3 11 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 253
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 253 (accept_3_3 8 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 253 (accept_3_3 5 205 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 205 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 253 (accept_3_3 2 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 205 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 253))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 204 253 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 204 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 48
  204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 204 253 (accept_3_3 47
  204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 253
  (Polychromatic418967fa.accept_13_7_9_6_1_148 46 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 204 253 (Polychromatic418967fa.accept_18_9_6_1_1_3687 45 204 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 253 (accept_3_3 44 204 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 204 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 253 (Polychromatic418967fa.accept_13_3_9_6_1_502
  42 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 204 253 (accept_3_3 41
  204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 204 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 204 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 253 (accept_3_3 38 204 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 204 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 253
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 204 253 (accept_3_3 35 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 204 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 204 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 253 (accept_3_3 32 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 204 253 (accept_3_3 29 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 204 253 (Polychromatic418967fa.accept_13_2_9_6_1_501 28 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 253 (accept_3_3 26 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 204 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 253
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 253 (accept_3_3 23 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 204 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 253 (accept_3_3 20 204 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 253 (Polychromatic418967fa.accept_10_9_4_3_1_539
  19 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 253
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 253 (accept_3_3 17 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 253 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 253 (accept_3_3 14 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 204 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 253 (accept_3_3 11 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 253 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 253 (accept_3_3 8 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 253
  (Polychromatic418967fa.accept_21_6_15_1_1_2050 6 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 253 (accept_3_3 5 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 204 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 253 (accept_3_3 2 204 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  253))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_253_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))


