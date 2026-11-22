-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch259
-- name    : Polychromatic418967fa_Branch259
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:30:28.043127+00:00
-- url     : https://prove2.me/theorems/182c67bf-8859-4a1f-9e8a-5f5eeb160db0
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch259_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_259 : allB 259 259 :=
  allB_succ' 2 258 259 (Eq.refl Bool.true) (allA_succ_of_accept 1 258 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  258 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 259)) (allB_succ' 3 257 259
  (Eq.refl Bool.true) (allA_of_3_1 3 257 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 256 259 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 256 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 256 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 256 259 (accept_3_3 2 256 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 256 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 256 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 259)))) (allB_succ' 5 255 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 255 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 255 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 259 (Polychromatic418967fa.accept_23_3_2_6_1_15828 3 255
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 259 (accept_3_3 2 255 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  255 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 259))))) (allB_succ' 6 254 259
  (Eq.refl Bool.true) (allA_of_3_1 6 254 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 253 259 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 253 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 253 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 259 (accept_3_3 5 253 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 253 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 253 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 259 (accept_3_3 2 253 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 259 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1 253 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 259))))))) (allB_succ' 8 252 259 (Eq.refl Bool.true) (allA_succ_of_gcd 7 252 259 7 1 36 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 252 259
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 252 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 252 259 (accept_3_3 5 252 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  252 259 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 252 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 252 259 (Polychromatic418967fa.accept_22_3_10_17_1_15827 3 252 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 259 (accept_3_3 2 252 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 252 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 259)))))))) (allB_succ' 9 251 259 (Eq.refl
  Bool.true) (allA_of_3_1 9 251 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 250 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 250 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 250 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 250 259 (accept_3_3 8 250 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 250 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 250 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 250 259 (Polychromatic418967fa.accept_15_6_10_4_1_150
  6 250 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 250 259 (accept_3_3 5
  250 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 250 259
  (Polychromatic418967fa.accept_12_4_10_7_1_149 4 250 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 250 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 250 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 259 (accept_3_3 2 250 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 250 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 250 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 259)))))))))) (allB_succ' 11 249 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 10 249 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 249 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 259 (Polychromatic418967fa.accept_19_9_2_12_1_6243 9 249
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 249 259 (accept_3_3 8 249 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 259 (Polychromatic418967fa.accept_16_7_9_3_1_1324
  7 249 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 249 259 (accept_3_3 5 249 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  249 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 249 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 249 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 249 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 259 (accept_3_3 2 249 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 249 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 259))))))))))) (allB_succ' 12 248 259 (Eq.refl
  Bool.true) (allA_of_3_1 12 248 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 247 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 247 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 247 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 259 (accept_3_3 11 247 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 247 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 247 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 259 (Polychromatic418967fa.accept_16_9_7_3_1_614 9
  247 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 259 (accept_3_3 8 247
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 259
  (Polychromatic418967fa.accept_23_7_17_6_1_9257 7 247 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 247 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 247 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 259 (accept_3_3 5 247 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 247 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 247 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  247 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 259 (accept_3_3 2 247
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 259 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 247 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 259))))))))))))) (allB_succ' 14
  246 259 (Eq.refl Bool.true) (allA_succ_of_accept 13 246 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 246 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 259
  (Polychromatic418967fa.accept_17_12_8_4_1_2518 12 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 246 259 (accept_3_3 11 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 246 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 246 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 246 259 (accept_3_3 8 246 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 259 (Polychromatic418967fa.accept_17_7_8_4_1_1520 7 246 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 246 259 (accept_3_3 5 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  246 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 246 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 246 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 246 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 246 259 (accept_3_3 2 246 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 246 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 259)))))))))))))) (allB_succ' 15 245 259 (Eq.refl
  Bool.true) (allA_of_3_1 15 245 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 244 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 244 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 244 259 (accept_3_3 14 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 244 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 244 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 244 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  244 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 244 259 (accept_3_3 11
  244 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 244 259
  (Polychromatic418967fa.accept_12_10_4_7_1_948 10 244 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 244 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 244 259 (accept_3_3 8 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 244 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 244 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 244 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  244 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 244 259 (accept_3_3 5 244
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 259
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 244 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 244 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 259 (accept_3_3 2 244 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 244 259 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 244 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 259)))))))))))))))) (allB_succ' 17 243 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 243 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 243 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 259 (Polychromatic418967fa.accept_21_15_12_7_1_5204 15 243
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 259 (accept_3_3 14 243
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 259
  (Polychromatic418967fa.accept_25_13_18_9_1_10603 13 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 243 259 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 243 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 259 (accept_3_3 11 243 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 243 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 243 259 (accept_3_3 8 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  243 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 243 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 243 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 259 (accept_3_3 5 243 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 243 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 259
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 259 (accept_3_3 2 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 243 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 259))))))))))))))))) (allB_succ' 18 242 259 (Eq.refl Bool.true) (allA_of_3_1 18 242 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 241 259 (Eq.refl Bool.true) (allA_succ_of_accept 18 241 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 241 259 (accept_3_3 17 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 241 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 241 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 241 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 259 (accept_3_3 14 241 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 259 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 241
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 259
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 259 (accept_3_3 11 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 259 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 241 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 259 (accept_3_3 8 241 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 259 (Polychromatic418967fa.accept_17_7_3_4_1_8563 7 241 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 259 (accept_3_3 5 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 241 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 259 (Polychromatic418967fa.accept_15_3_1_4_1_1246 3 241 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 259 (accept_3_3 2 241 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 259 (Polychromatic418967fa.accept_19_1_13_12_1_7748 1 241 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 259))))))))))))))))))) (allB_succ' 20 240 259
  (Eq.refl Bool.true) (allA_succ_of_accept 19 240 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 240 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 259
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 259 (accept_3_3 17 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 240 259 (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 259 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 240 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 259 (accept_3_3 14 240 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 240 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 240 259 (accept_3_3 11 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 240 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 240 259 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 240 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 259 (accept_3_3 8 240 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 240 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 259
  (Polychromatic418967fa.accept_17_6_2_4_1_2421 6 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 240 259 (accept_3_3 5 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  240 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 240 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 240 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 240 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 259 (accept_3_3 2 240 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 240 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 259)))))))))))))))))))) (allB_succ' 21 239 259
  (Eq.refl Bool.true) (allA_of_3_1 21 239 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 238 259 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 238 259 7 3 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 238 259 (accept_3_3 20 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 238 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 238 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 238 259 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 238
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 238 259 (accept_3_3 17 238
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 238 259
  (Polychromatic418967fa.accept_12_4_10_7_1_149 16 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 238 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 238 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 238 259 7 2 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 238 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 238 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 238 259 (accept_3_3 11 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 238 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 238 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 238 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 238 259 (accept_3_3 8 238 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 238 259 7 1 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 238 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 238 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 259 (accept_3_3 5 238 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 238 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 238 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 238 259 (accept_3_3 2 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  238 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 238 259)))))))))))))))))))))) (allB_succ' 23 237 259 (Eq.refl Bool.true) (allA_succ_of_accept 22
  237 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 237 259 (Polychromatic418967fa.accept_19_2_9_12_1_2237 21 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 259 (accept_3_3 20 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 237 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 237 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 237 259 (accept_3_3 17 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 237 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 237 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 237 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 259 (accept_3_3 14 237 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 259
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 237 259 (accept_3_3 11 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 237 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 237 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 259 (accept_3_3 8 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 237
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 237 259 (accept_3_3 5 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  237 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 237 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 237 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 259 (accept_3_3 2 237 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 237 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 259))))))))))))))))))))))) (allB_succ' 24 236 259
  (Eq.refl Bool.true) (allA_of_3_1 24 236 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 235 259 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 235 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 259 (accept_3_3 23 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 235 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 259 (accept_3_3 20 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 259 (Polychromatic418967fa.accept_21_19_4_7_1_3775 19 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 235 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 259 (accept_3_3 17 235 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 235
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 235 259 (accept_3_3 14 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 235 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 259 (accept_3_3 11 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 259 (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 235 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 259
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 259 (accept_3_3 8 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 259 (accept_3_3 5 235 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 259 (accept_3_3 2 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 235 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 259))))))))))))))))))))))))) (allB_succ' 26 234 259 (Eq.refl Bool.true) (allA_succ_of_accept
  25 234 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 234 259 (Polychromatic418967fa.accept_20_4_14_19_1_4222 24 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 234 259 (accept_3_3 23 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 234 259 (Polychromatic418967fa.accept_21_1_3_7_1_3727 22 234
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 234 259 (accept_3_3 20 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 234 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 234 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 259 (accept_3_3 17 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 259 (Polychromatic418967fa.accept_19_16_6_12_1_11776 16
  234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 259
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 234 259 (accept_3_3 14 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 234 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 234 259 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 259 (accept_3_3 11 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 259 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 234
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 234 259 (accept_3_3 8 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  234 259 (Polychromatic418967fa.accept_16_7_10_3_1_2210 7 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 234 259 (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 234 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 259 (accept_3_3 5 234 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 259 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 234 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 259
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 234 259 (accept_3_3 2 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  234 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 259)))))))))))))))))))))))))) (allB_succ' 27 233 259 (Eq.refl Bool.true) (allA_of_3_1 27 233
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 232 259 (Eq.refl Bool.true) (allA_succ_of_accept 27 232
  259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 232 259 (accept_3_3 26 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 232 259 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 232 259 (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 232 259 (accept_3_3 23 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 232 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 232
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 232 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 232 259 (accept_3_3 20 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 232 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 232 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 232 259 (accept_3_3 17 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 232 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 232
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 232 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 232 259 (accept_3_3 14 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 232 259 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 232 259 (Polychromatic418967fa.accept_15_12_7_4_1_2921 12 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 232 259 (accept_3_3 11 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 232
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 232 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 232 259 (accept_3_3 8 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  232 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 232 259 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 232 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 259 (accept_3_3 5 232 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 259 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 232 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 232 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 232 259 (accept_3_3 2 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  232 259 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 232 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 232 259)))))))))))))))))))))))))))) (allB_succ' 29 231 259 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 231 259 7 4 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 231 259 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 231 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 259 (accept_3_3 26 231 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 231 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 231 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 259
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 259 (accept_3_3 23 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 231 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 231 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 231 259 7 3 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 231 259 (accept_3_3 20 231 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 231 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 231 259
  (Polychromatic418967fa.accept_10_8_1_9_1_413 18 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 231 259 (accept_3_3 17 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 231 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 231 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 231 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 231 259 7 2 33 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 231 259
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 231 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 231 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 259 (accept_3_3 11 231 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 231 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 231 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 259 (accept_3_3 8 231
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 231 259 7 1 33 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 231 259
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 231 259 (accept_3_3 5 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  231 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 231 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 231 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 259 (accept_3_3 2 231 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 231 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 259))))))))))))))))))))))))))))) (allB_succ' 30 230
  259 (Eq.refl Bool.true) (allA_of_3_1 30 230 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 229 259
  (Eq.refl Bool.true) (allA_succ_of_accept 30 229 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 259 (accept_3_3 29 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 229 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 259
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 229 259 (accept_3_3 26 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 259 (accept_3_3 23 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 259 (accept_3_3 20 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 259 (accept_3_3 17 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 259 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 259 (accept_3_3 14 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 259 (Polychromatic418967fa.accept_17_13_8_4_1_2514 13 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 259 (accept_3_3 11 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 259
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 259 (accept_3_3 8 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 259 (accept_3_3 5 229 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 229 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 259 (accept_3_3 2 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 229 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 259))))))))))))))))))))))))))))))) (allB_succ' 32 228 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 228 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 228 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 228 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 228
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 228 259 (accept_3_3 29 228
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 259 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 259
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 228 259 (accept_3_3 26 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 228 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 228 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 228 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 228 259 (accept_3_3 23 228 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 259
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 228 259 (accept_3_3 20 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 228 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 228 259 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 259 (accept_3_3 17 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 228
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 259
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 228 259 (accept_3_3 14 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 228 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 228 259 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 259 (accept_3_3 11 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 228 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 259
  (Polychromatic418967fa.accept_20_9_8_19_1_802 9 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 228 259 (accept_3_3 8 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  228 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 228 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 228 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 259 (accept_3_3 5 228 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 228 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 259
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 228 259 (accept_3_3 2 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  228 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 228 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 259)))))))))))))))))))))))))))))))) (allB_succ' 33 227 259 (Eq.refl Bool.true) (allA_of_3_1
  33 227 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 226 259 (Eq.refl Bool.true) (allA_succ_of_accept 33
  226 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 226 259 (accept_3_3 32 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 226 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 226 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 226 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 226 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 226 259 (accept_3_3 29 226 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 226 259 (Polychromatic418967fa.accept_12_4_10_7_1_149
  28 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 226 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 226 259 (accept_3_3 26 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 226 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 226 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 226 259 (accept_3_3 23 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 226 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 226 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 226 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 226 259 (accept_3_3 20 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 226 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 226 259 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 226 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 226 259 (accept_3_3 17 226 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 226 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 226
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 226 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 226 259 (accept_3_3 14 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 226 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 226 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 226 259 (accept_3_3 11 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 226 259 (Polychromatic418967fa.accept_19_10_17_12_1_2271 10 226 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 226 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 226 259 (accept_3_3 8 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  226 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 226 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 226 259 (accept_3_3 5 226 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 226 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 226 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 226 259 (accept_3_3 2 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  226 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 226 259)))))))))))))))))))))))))))))))))) (allB_succ' 35 225 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 225 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 225
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 259 (accept_3_3 32 225
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 225 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 259 (accept_3_3 29 225 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 225 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 225 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 259 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 259 (accept_3_3 26
  225 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 259
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 25 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 259 (accept_3_3 23 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 225 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 259
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 259 (accept_3_3 20 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 259 (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 259 (accept_3_3 17 225 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 259 (accept_3_3 14 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 225 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 259 (accept_3_3 11 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 225 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 259
  (Polychromatic418967fa.accept_19_9_16_12_1_4760 9 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 259 (accept_3_3 8 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 259 (accept_3_3 5 225 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 259 (accept_3_3 2 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 225 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 259))))))))))))))))))))))))))))))))))) (allB_succ' 36 224 259 (Eq.refl Bool.true)
  (allA_of_3_1 36 224 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 223 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 223 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 223 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 259 (accept_3_3 35 223 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 223 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 259
  (Polychromatic418967fa.accept_23_10_16_6_1_15826 33 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 223 259 (accept_3_3 32 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 223 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 223 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 223 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 223
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 259 (accept_3_3 29 223
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 223 259 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 223 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 259 (accept_3_3 26 223 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 223 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 259
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 223 259 (accept_3_3 23 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 223 259 (Polychromatic418967fa.accept_14_8_13_7_1_2798 22 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 223 259 (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 259 (accept_3_3 20 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 259 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 223
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 259
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 259 (accept_3_3 17 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 259 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 259 (accept_3_3 14 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 223
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 259 (accept_3_3 11 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 259 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 223 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 259 (accept_3_3 8 223 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 259 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 259
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 259 (accept_3_3 5 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 223 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 259 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 259 (accept_3_3 2 223 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 259 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 223
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223
  259))))))))))))))))))))))))))))))))))))) (allB_succ' 38 222 259 (Eq.refl Bool.true) (allA_succ_of_gcd 37 222 259 37 1
  6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 36 222 259
  (Polychromatic418967fa.accept_21_15_12_7_1_5204 36 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 222 259 (accept_3_3 35 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 222 259 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 222 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 259 (accept_3_3 32 222 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 259 (Polychromatic418967fa.accept_9_4_6_7_1_286
  31 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 222 259 (accept_3_3 29 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 222 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 259 (accept_3_3 26 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 222 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 259
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 222 259 (accept_3_3 23 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 222 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 259 (accept_3_3 20 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 259
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 222 259 (accept_3_3 17 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 222 259 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 222 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 259 (accept_3_3 14 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 222 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 259 (accept_3_3 11 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 222 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 259 (accept_3_3 8 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 259
  (Polychromatic418967fa.accept_19_6_13_12_1_6220 6 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 259 (accept_3_3 5 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  222 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 222 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 259 (accept_3_3 2 222 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 259))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 221 259 (Eq.refl Bool.true) (allA_of_3_1 39 221 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 220 259 (Eq.refl Bool.true) (allA_succ_of_accept 39 220 259 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 220 259 (accept_3_3 38
  220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 220 259
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 220 259 (Polychromatic418967fa.accept_15_6_10_4_1_150 36 220 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 220 259 (accept_3_3 35 220 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 220 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 220 259 (accept_3_3 32 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 220 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 220 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 220 259 (accept_3_3 29 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 259 (accept_3_3 26 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 220 259 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 220 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 220 259 (accept_3_3 23 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 220 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 220 259 (accept_3_3 20 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 220 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 220 259 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 259 (accept_3_3 17 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 220 259 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 220
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 220 259 (accept_3_3 14 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 259 (accept_3_3 11 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 220 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 259 (accept_3_3 8 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 259 (accept_3_3 5 220 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 259 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 220 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 259 (accept_3_3 2 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 220 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 259)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 219 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 259 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 219
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 259 (accept_3_3 38 219
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 259 (Polychromatic418967fa.accept_9_1_3_7_1_6
  37 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 259
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 259 (accept_3_3 35 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 219 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 259 (accept_3_3 32 219 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 259 (Polychromatic418967fa.accept_9_4_3_7_1_296
  31 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 259
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 259 (accept_3_3 29 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 219
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 259 (accept_3_3 26 219
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 259
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 219 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 259 (accept_3_3 23 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 219 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 259 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 259 (accept_3_3 20
  219 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 259
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 219 259 (Polychromatic418967fa.accept_21_18_9_7_1_3700 18 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 259 (accept_3_3 17 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 259 (Polychromatic418967fa.accept_9_6_3_7_1_580
  15 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 259 (accept_3_3 14
  219 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 259
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 219 259 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 259 (accept_3_3 11 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 219 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 259 (accept_3_3 8 219
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 259
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 219 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 259 (accept_3_3 5 219 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 219 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 259
  (Polychromatic418967fa.accept_19_3_10_12_1_6217 3 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 259 (accept_3_3 2 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 219 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 259))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 218 259 (Eq.refl Bool.true)
  (allA_of_3_1 42 218 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 217 259 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 217 259 7 6 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 217 259 (accept_3_3 41 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 217 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 217 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 217 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 259 (accept_3_3 38 217 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 217 259 (Polychromatic418967fa.accept_17_3_13_4_1_8530 37 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 217 259
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 217 259 7 5 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 217 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 217 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 259 (accept_3_3 32 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 259 (Polychromatic418967fa.accept_9_4_1_7_1_293
  31 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 259 (accept_3_3 29 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  217 259 7 4 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 217 259 (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 217 259 (accept_3_3 26 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 217 259 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 217 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 259 (accept_3_3 23 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 217 259 7 3 31 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 217 259 (accept_3_3 20
  217 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 259
  (Polychromatic418967fa.accept_23_19_10_6_1_12573 19 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 259 (accept_3_3 17 217 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 217 259 7 2 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 217 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 259 (accept_3_3 11 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 259
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 259 (accept_3_3 8 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 217
  259 7 1 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  217 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 217 259 (accept_3_3 5 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 217 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 259 (accept_3_3 2 217 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 259 (Polychromatic418967fa.accept_19_1_8_12_1_6149
  1 217 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217
  259))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 216 259 (Eq.refl Bool.true) (allA_succ_of_accept 43 216
  259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 216 259 (Polychromatic418967fa.accept_17_8_12_4_1_2525 42 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 216 259 (accept_3_3 41 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 259 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 259
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 216 259 (accept_3_3 38 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 216 259 (Polychromatic418967fa.accept_16_5_8_3_1_4240 37 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 216 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 216 259 (accept_3_3 35 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 259
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 216 259 (accept_3_3 32 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 216 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 216 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 216 259 (accept_3_3 29 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 259 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 259
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 216 259 (accept_3_3 26 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 216 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 216 259 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 216 259 (accept_3_3 23 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 259 (Polychromatic418967fa.accept_13_9_8_12_1_2031 22 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 259
  (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 216 259 (accept_3_3 20 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 216 259 (Polychromatic418967fa.accept_17_2_12_4_1_5987 19 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 216 259 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 216 259 (accept_3_3 17 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 259 (Polychromatic418967fa.accept_19_16_7_12_1_6252 16 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 259
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 216 259 (accept_3_3 14 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 216 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 216 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 259 (accept_3_3 11 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 259 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 259
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 216 259 (accept_3_3 8 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  216 259 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 216 259 (Polychromatic418967fa.accept_25_6_16_9_1_12250 6 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 259 (accept_3_3 5 216 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 259 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 216
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 259
  (Polychromatic418967fa.accept_10_3_6_9_1_779 3 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 216 259 (accept_3_3 2 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  216 259 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 216 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 216 259)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 215 259 (Eq.refl Bool.true)
  (allA_of_3_1 45 215 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 214 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 214 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 214 259 (accept_3_3 44 214 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 214 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 214 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 214 259
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 214 259 (accept_3_3 41 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 214 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 214 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 214 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 259 (accept_3_3 38 214 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 214 259
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 214 259 (accept_3_3 35 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 214 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 214 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 214 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 259 (accept_3_3 32 214 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 259
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 214 259 (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 214 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 214 259 (accept_3_3 29 214 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 214 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 214 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 214 259 (accept_3_3 26 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 214 259 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 214 259 (accept_3_3 23 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 214 259 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 214
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 214 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 214 259 (accept_3_3 20 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 214 259 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 214 259 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 214 259 (accept_3_3 17 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 214 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 214
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 214 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 214 259 (accept_3_3 14 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 214 259 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 214 259 (accept_3_3 11 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 214 259 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 214
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 214 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 259 (accept_3_3 8 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 259 (Polychromatic418967fa.accept_17_6_10_4_1_6007 6 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 259 (accept_3_3 5 214 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 214 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 259 (accept_3_3 2 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 259)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 213 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 213 259 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 213
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 259 (accept_3_3 44 213
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 259
  (Polychromatic418967fa.accept_13_4_5_12_1_751 43 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 259 (accept_3_3 41 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 213 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 259 (Polychromatic418967fa.accept_9_3_6_7_1_562
  39 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 259 (accept_3_3 38
  213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 213 259 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 259 (accept_3_3 35 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 259
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 213 259 (accept_3_3 32 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 213 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 259 (accept_3_3 29 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 213 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 259 (accept_3_3 26 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 259 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 259 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 213 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 259 (accept_3_3 23 213 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 213 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 259 (accept_3_3 20 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 259 (accept_3_3 17 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 259
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 259 (accept_3_3 14 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 259 (accept_3_3 11 213 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 259
  (Polychromatic418967fa.accept_20_9_13_19_1_10072 9 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 259 (accept_3_3 8 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 259 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 213 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 259 (accept_3_3 5 213 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 259 (accept_3_3 2 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 213 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 259))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 212 259 (Eq.refl
  Bool.true) (allA_of_3_1 48 212 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 211 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 211 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 211 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 211 259 (accept_3_3 47 211 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 211 259 (Polychromatic418967fa.accept_10_5_1_9_1_791
  45 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 259 (accept_3_3 44
  211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 259
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 211 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 211 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 259 (accept_3_3 41 211 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 211 259 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 211 259 (accept_3_3 38 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 211 259 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 259 (accept_3_3 35 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 259 (Polychromatic418967fa.accept_14_6_1_7_1_2775 34 211
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 259 (accept_3_3 32 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 259 (Polychromatic418967fa.accept_17_14_7_4_1_3476 31 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 259 (accept_3_3 29 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 259
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 259 (accept_3_3 26 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 259 (accept_3_3 23 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 259 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 259 (accept_3_3 20 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 259 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 259 (accept_3_3 17 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 259 (Polychromatic418967fa.accept_21_16_1_7_1_6725 16 211
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 259 (accept_3_3 14 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 259 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 259 (accept_3_3 11 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 259
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 259 (accept_3_3 8 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 259 (Polychromatic418967fa.accept_22_7_13_17_1_9708 7 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 259 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 259 (accept_3_3 5 211 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 259 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 211 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 259 (accept_3_3 2 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 211 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 259))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 210 259 (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 210 259 7 7 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 48 210 259 (Polychromatic418967fa.accept_23_2_3_6_1_15825 48 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 210 259 (accept_3_3 47 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 210 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 210 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 210 259 (accept_3_3 44 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 210 259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 210 259 7 6 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 210 259 (accept_3_3 41 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 210 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 210 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 259 (Polychromatic418967fa.accept_17_5_6_4_1_8607 39 210
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 259 (accept_3_3 38 210
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 259 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 259
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 210 259 7 5 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 210 259 (Polychromatic418967fa.accept_23_11_3_6_1_15824 34 210 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 210 259 (accept_3_3 32 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 210 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 210 259 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 210 259 (accept_3_3 29 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 259 7 4 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 259 (Polychromatic418967fa.accept_11_5_1_6_1_774
  27 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 259 (accept_3_3 26
  210 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 210 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 210 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 259 (accept_3_3 23 210 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 210 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 210 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 210 259 7 3 30 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 210 259 (accept_3_3 20 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 210 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 259
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 259 (accept_3_3 17 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 210 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 210 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 210 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 259 7 2 30 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 210 259 (Polychromatic418967fa.accept_24_12_18_19_1_15823 12 210 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 259 (accept_3_3 11 210 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 210 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 259
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 210 259 (accept_3_3 8 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 210
  259 7 1 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  210 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 210 259 (accept_3_3 5 210 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 210 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 210 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 259 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 210
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 259 (accept_3_3 2 210 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  210 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  259)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 209 259 (Eq.refl Bool.true) (allA_of_3_1 51 209
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 208 259 (Eq.refl Bool.true) (allA_succ_of_accept 51 208
  259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 208 259 (accept_3_3 50 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 208 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 208 259 (accept_3_3 47 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 208 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 208 259 (accept_3_3 44 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 208 259 (Polychromatic418967fa.accept_21_1_19_7_1_1218 43 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 208 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 259 (accept_3_3 41 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 259 (accept_3_3 38 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 259 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 259 (accept_3_3 35 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 208
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 259 (accept_3_3 32 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 259 (accept_3_3 29 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 259 (Polychromatic418967fa.accept_19_9_18_12_1_2286 28 208 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 259 (accept_3_3 26 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 259 (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 259 (accept_3_3 23 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 259 (accept_3_3 20 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 259 (Polychromatic418967fa.accept_14_5_12_7_1_2767 19 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 259 (Polychromatic418967fa.accept_21_18_19_7_1_5165 18 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 259 (accept_3_3 17 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 259 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 208
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 259 (accept_3_3 14 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 208 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 259 (accept_3_3 11 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 259 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 259 (accept_3_3 8 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 259 (accept_3_3 5 208 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 208 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 259 (accept_3_3 2 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 208 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 259)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 207 259 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 259
  (Polychromatic418967fa.accept_21_9_18_7_1_5180 51 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 207 259 (accept_3_3 50 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 207 259 (Polychromatic418967fa.accept_27_22_18_16_1_15790 49 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 259 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 259 (accept_3_3 47 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 207 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 207 259 (accept_3_3 44 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 207 259 (Polychromatic418967fa.accept_16_11_15_3_1_1304 43 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 207 259 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 259 (accept_3_3 41 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 207 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 259
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 39 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 207 259 (accept_3_3 38 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 207 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 37 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 207 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 259 (accept_3_3 35 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 259
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 207 259 (accept_3_3 32 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 207 259 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 207 259 (Polychromatic418967fa.accept_17_13_3_4_1_2537 30 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 259 (accept_3_3 29 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 259
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 259 (accept_3_3 26 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 207 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 259 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 207
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 259 (accept_3_3 23 207
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 259
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 207 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 207 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 259 (accept_3_3 20 207 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 207 259 (Polychromatic418967fa.accept_21_19_18_7_1_8388 19 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 259
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 207 259 (accept_3_3 17 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 259 (Polychromatic418967fa.accept_19_15_17_12_1_7723 15 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 259 (accept_3_3 14 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 259 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 207
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 259 (accept_3_3 11 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 259 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 259 (accept_3_3 8 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 259 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 259
  (Polychromatic418967fa.accept_18_6_9_7_1_2905 6 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 259 (accept_3_3 5 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 259 (accept_3_3 2 207 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 259 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 207 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  259))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 206 259 (Eq.refl Bool.true) (allA_of_3_1 54
  206 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 205 259 (Eq.refl Bool.true) (allA_succ_of_accept 54
  205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 205 259 (accept_3_3 53 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 205 259 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 205 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 205
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 205 259 (accept_3_3 50 205
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 205 259
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 205 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 259 (accept_3_3 47 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 259
  (Polychromatic418967fa.accept_11_1_7_6_1_378 45 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 205 259 (accept_3_3 44 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 259 (accept_3_3 41 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 259 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 205 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 259
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 259 (accept_3_3 38 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 259 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 259 (accept_3_3 35 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 205 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 259
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 205 259 (accept_3_3 32 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 205 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 205 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 205 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 259 (accept_3_3 29 205 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 259
  (Polychromatic418967fa.accept_13_2_10_12_1_757 28 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 205 259 (Polychromatic418967fa.accept_19_8_15_12_1_2240 27 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 259 (accept_3_3 26 205 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 259 (Polychromatic418967fa.accept_17_8_1_4_1_9831 25 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 259
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 259 (accept_3_3 23 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 259 (accept_3_3 20 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 259 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 205
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 259 (accept_3_3 17 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 259 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 259 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 259 (accept_3_3 14 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 259 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 205
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 259
  (Polychromatic418967fa.accept_11_1_7_6_1_378 12 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 259 (accept_3_3 11 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 259 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 259 (accept_3_3 8 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 259 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 205
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 259 (accept_3_3 5 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 259 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 205 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 259 (Polychromatic418967fa.accept_19_3_15_12_1_9110 3 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 259 (accept_3_3 2 205 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 259 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 205 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 204 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 204 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 259 (Polychromatic418967fa.accept_19_16_14_12_1_6261 54
  204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 204 259 (accept_3_3 53
  204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 259
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 204 259 (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 259 (accept_3_3 50 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 204 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 259 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 204 259 (accept_3_3 47
  204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 259
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 204 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 259 (accept_3_3 44 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 204 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 259
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 204 259 (accept_3_3 41 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 204 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 204 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 259 (accept_3_3 38 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 259
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 204 259 (accept_3_3 35 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 204 259 (Polychromatic418967fa.accept_13_8_9_12_1_2813 34 204 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 204 259 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 204 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 259 (accept_3_3 32 204 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 259 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 204 259 (accept_3_3 29 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 204 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 259 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 259 (accept_3_3 26 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 259 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 204
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 259
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 204 259 (accept_3_3 23 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 204 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 204 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 259 (accept_3_3 20 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 259
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 259 (accept_3_3 17 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 259 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 259 (accept_3_3 14 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 259
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 259 (accept_3_3 11 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 259 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 259 (accept_3_3 8 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 204 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 259
  (Polychromatic418967fa.accept_14_6_8_7_1_589 6 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 259 (accept_3_3 5 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 259 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 204 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 259 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 259 (accept_3_3 2 204 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 259 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 203 259 (Eq.refl Bool.true) (allA_of_3_1 57
  203 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 202 259 (Eq.refl Bool.true) (allA_succ_of_accept 57
  202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 202 259 (accept_3_3 56 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 202 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 202 259 (Polychromatic418967fa.accept_22_10_4_17_1_7993 54 202
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 202 259 (accept_3_3 53 202
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 202 259
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 202 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 259 (accept_3_3 50 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 259 (Polychromatic418967fa.accept_9_3_4_7_1_89 48
  202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 202 259 (accept_3_3 47
  202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 202 259
  (Polychromatic418967fa.accept_9_1_4_7_1_7 46 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 259 (accept_3_3 44 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 202 259 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 202 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 202 259 (accept_3_3 41 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 202 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 202 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 259 (accept_3_3 38 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 202 259
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 202 259 (accept_3_3 35 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 202 259 (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 202 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 202 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 259 (accept_3_3 32 202 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 259 (Polychromatic418967fa.accept_10_1_2_9_1_152
  31 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 259 (accept_3_3 29 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 259 (accept_3_3 26 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 259 (accept_3_3 23 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 259 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 259 (accept_3_3 20 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 259
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 259 (accept_3_3 17 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 259 (accept_3_3 14 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 259
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 259 (accept_3_3 11 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 259 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 259 (accept_3_3 8 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 259 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 259
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 259 (accept_3_3 5 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 259 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 202 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 259 (accept_3_3 2 202 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 201 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 201 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 201 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 259 (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 201
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 259 (accept_3_3 56 201
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 259 (Polychromatic418967fa.accept_9_1_3_7_1_6
  55 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 201 259 (accept_3_3 53 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 201 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 201 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 259 (accept_3_3 50 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 259
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 201 259 (accept_3_3 47 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 201 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 201 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 259 (accept_3_3 44 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 259 (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 201
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 201 259 (accept_3_3 41 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 201 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 201 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 259 (accept_3_3 38 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 201 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 259
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 259 (accept_3_3 35 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 201 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 201 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 259 (accept_3_3 32 201 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 259 (Polychromatic418967fa.accept_9_4_3_7_1_296
  31 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 259 (accept_3_3 29 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 201 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 259 (accept_3_3 26 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 259 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 201
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 259
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 259 (accept_3_3 23 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 201 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 259 (Polychromatic418967fa.accept_23_21_17_6_1_7541 21 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 259 (accept_3_3 20 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 201 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 201 259 (accept_3_3 17 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 201 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 259 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 259 (accept_3_3 14 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 259 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 259
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 259 (accept_3_3 11 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 201 259 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 259 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 259 (accept_3_3 8 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 259 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 259
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 259 (accept_3_3 5 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 259 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 259 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 259 (accept_3_3 2 201 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 259 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 201 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 200 259 (Eq.refl Bool.true) (allA_of_3_1
  60 200 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 199 259 (Eq.refl Bool.true) (allA_succ_of_accept 60
  199 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 199 259 (accept_3_3 59 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 199 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 199 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 199 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 259 (accept_3_3 56 199 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 259 (Polychromatic418967fa.accept_13_3_4_12_1_36
  55 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 259
  (Polychromatic418967fa.accept_13_2_4_12_1_745 54 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 259 (accept_3_3 53 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 259 (accept_3_3 50 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 259 (accept_3_3 47 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 259 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 259 (Polychromatic418967fa.accept_21_3_10_7_1_14215 45 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 259 (accept_3_3 44 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 259 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 199
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 259 (accept_3_3 41 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 259 (accept_3_3 38 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 259 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 199 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 259 (accept_3_3 35 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 259 (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 259 (accept_3_3 32 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 259
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 259 (accept_3_3 29 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 259 (accept_3_3 26 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 259 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 199
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 259 (accept_3_3 23 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 259 (accept_3_3 20 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 259 (Polychromatic418967fa.accept_17_2_12_4_1_5987 19 199 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 259
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 259 (accept_3_3 17 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 259 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 259 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 259 (accept_3_3 14 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 259 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 259
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 259 (accept_3_3 11 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 259 (Polychromatic418967fa.accept_14_10_3_7_1_1975 10 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 259 (Polychromatic418967fa.accept_16_9_7_3_1_614 9 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 259 (accept_3_3 8 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 259 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 259
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 259 (accept_3_3 5 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 259 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 199 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 259 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 259 (accept_3_3 2 199 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 259 (Polychromatic418967fa.accept_19_1_9_12_1_6207 1 199 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 198 259 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 198 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 259 (Polychromatic418967fa.accept_21_18_9_7_1_3700 60 198
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 198 259 (accept_3_3 59 198
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 259
  (Polychromatic418967fa.accept_19_1_8_12_1_6149 58 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 259 (accept_3_3 56 198 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 198 259 (Polychromatic418967fa.accept_21_13_9_7_1_9858 55 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 198 259
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 198 259 (accept_3_3 53 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 198 259 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 198 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 259 (accept_3_3 50 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 198 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 198 259
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 198 259 (accept_3_3 47 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 198 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 259 (accept_3_3 44 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 259 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 198 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 259
  (Polychromatic418967fa.accept_19_4_8_12_1_4757 42 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 198 259 (accept_3_3 41 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 198 259 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 198 259 (Polychromatic418967fa.accept_19_1_8_12_1_6149 39 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 259 (accept_3_3 38 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 198 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 259
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 198 259 (accept_3_3 35 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 198 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 259 (accept_3_3 32 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 259 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 259
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 198 259 (accept_3_3 29 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 198 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 198 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 259 (accept_3_3 26 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 198 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 259
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 259 (accept_3_3 23 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 259 (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 259 (accept_3_3 20 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 259 (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 259
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 259 (accept_3_3 17 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 259 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 259 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 259 (accept_3_3 14 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 259
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 259
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 259 (accept_3_3 11 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 259 (Polychromatic418967fa.accept_17_10_11_4_1_2522 10 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 259 (accept_3_3 8 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 259 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 259
  (Polychromatic418967fa.accept_17_6_11_4_1_1525 6 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 259 (accept_3_3 5 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 259 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 198 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 259 (Polychromatic418967fa.accept_21_3_9_7_1_8369 3 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 259 (accept_3_3 2 198 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 259 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  259)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 197 259 (Eq.refl Bool.true)
  (allA_of_3_1 63 197 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 196 259 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 196 259 7 9 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 196 259 (accept_3_3 62 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 196 259 (Polychromatic418967fa.accept_19_4_6_12_1_13144 61 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 196 259 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 196 259 (accept_3_3 59 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 196 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 58 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 196 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 196 259 7 8 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 196 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 196 259 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 196 259 (accept_3_3 53 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 196 259
  (Polychromatic418967fa.accept_19_14_6_12_1_13167 52 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 196 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 196 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 196 259 (accept_3_3 50 196 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 196 259 7 7 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 196 259 (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 196 259 (accept_3_3 47 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 196 259
  (Polychromatic418967fa.accept_12_10_4_7_1_948 46 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 196 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 259 (accept_3_3 44 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 196 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 196 259 7 6 28 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 196 259 (accept_3_3 41 196 259
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 196 259 (Polychromatic418967fa.accept_16_8_4_3_1_3146
  40 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 196 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 196 259 (accept_3_3 38 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 196 259 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 196 259 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 196 259 7 5 28 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 196 259
  (Polychromatic418967fa.accept_12_10_4_7_1_948 34 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 196 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 259 (accept_3_3 32 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 196 259 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 196 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 259
  (Polychromatic418967fa.accept_17_13_9_4_1_5979 30 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 259 (accept_3_3 29 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  196 259 7 4 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 196 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 196 259 (accept_3_3 26 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 196 259 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 259 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 196 259 (accept_3_3 23 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 196 259
  (Polychromatic418967fa.accept_12_10_4_7_1_948 22 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 196 259 7 3 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 196 259 (accept_3_3 20 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 196 259 (Polychromatic418967fa.accept_17_2_9_4_1_3463 19 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 196 259 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 259 (accept_3_3 17 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 259 (Polychromatic418967fa.accept_19_16_6_12_1_11776 16
  196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 196 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 196 259 7 2 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 196 259 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 259 (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 259 (accept_3_3 11 196
  259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 259
  (Polychromatic418967fa.accept_12_10_4_7_1_948 10 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 196 259 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 259 (accept_3_3 8 196 259 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 196 259 7 1 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 196 259 (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 196 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 259 (accept_3_3 5 196 259 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 259 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 196 259 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 259
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 259 (accept_3_3 2 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 259 (Polychromatic418967fa.accept_16_1_4_3_1_3148 1 196 259 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 259))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_259_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


