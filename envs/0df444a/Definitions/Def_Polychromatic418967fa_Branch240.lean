-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch240
-- name    : Polychromatic418967fa_Branch240
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:36.725726+00:00
-- url     : https://prove2.me/theorems/2f04c2a6-2596-4a6f-86fa-2c7d453d49b3
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch240_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_240 : allB 240 240 :=
  allB_succ' 2 239 240 (Eq.refl Bool.true) (allA_succ_of_accept 1 239 240 (accept_3_4 1 239 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 240)) (allB_succ' 3 238 240 (Eq.refl Bool.true) (allA_succ_of_gcd 2 238 240 2 1 119
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 238 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 240))) (allB_succ' 4 237 240 (Eq.refl Bool.true) (allA_succ_of_gcd 3 237 240 3 1 79 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 237 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 237 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 237 240)))) (allB_succ' 5 236 240 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  236 240 4 1 59 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 236 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 236 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 236 240 2 1 118 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 236 240 (accept_3_4 1 236 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 236 240))))) (allB_succ' 6 235 240 (Eq.refl Bool.true) (allA_succ_of_gcd 5 235 240 5 1 47 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 235 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 235 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 235 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 235 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 240 (accept_3_5 2 235 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 235 240 (Polychromatic418967fa.accept_19_1_7_12_1_3443 1 235 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 240)))))) (allB_succ' 7 234 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 234 240 6 1 39 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 234 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 240 2 2 117 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 240 3 1 78 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 240 2 1 117 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 234 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 240))))))) (allB_succ' 8 233 240 (Eq.refl Bool.true) (allA_succ_of_accept 7 233 240 (accept_3_4 7 233
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 240
  (Polychromatic418967fa.accept_17_6_12_2_1_10966 6 233 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 233 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 233 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 240 (accept_3_4 4 233 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 233 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 233 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 2
  233 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 240 (accept_3_4 1 233
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233 240)))))))) (allB_succ' 9 232 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 232 240 8 1 29 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 232 240 (Polychromatic418967fa.accept_19_7_4_12_1_4769 7 232 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 240 2 3 116 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 240 (accept_3_5 5 232 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 240 4 1 58 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 232 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 232 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 240 2 1 116 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 232 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 240))))))))) (allB_succ' 10 231 240 (Eq.refl Bool.true) (allA_succ_of_gcd 9 231 240 3 3 77 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 240
  (Polychromatic418967fa.accept_17_8_10_2_1_4546 8 231 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 240 (Polychromatic418967fa.accept_19_7_3_12_1_4787 7 231 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 240 3 2 77 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 231 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 240
  (Polychromatic418967fa.accept_13_4_10_6_1_989 4 231 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 231 240 3 1 77 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 231 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 231 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 240 (Polychromatic418967fa.accept_27_1_15_24_1_14475 1 231
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 240)))))))))) (allB_succ' 11 230 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 230 240 10 1 23 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 240 (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 230 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 240 2 4 115 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 240 (accept_3_4 7
  230 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 240 2 3 115 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 230 240 5 1 46 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 230 240 2 2 115 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 230 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 240 2 1 115 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 240 (accept_3_4 1 230 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  240))))))))))) (allB_succ' 12 229 240 (Eq.refl Bool.true) (allA_succ_of_accept 11 229 240 (accept_3_5 11 229 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 10
  229 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 9 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 240 (accept_3_5 8 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 240 (Polychromatic418967fa.accept_22_6_9_20_1_14440 6 229 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 240 (accept_3_5 5 229 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 229 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 240 (accept_3_5 2 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 229 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 240)))))))))))) (allB_succ' 13 228 240 (Eq.refl Bool.true) (allA_succ_of_gcd 12 228 240 12 1
  19 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 228 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 228 240 2 5 114 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 228 240 3 3 76 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 228 240 4 2 57 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 228 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 228 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 240 6 1 38 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  228 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 240 4 1 57 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 240 3 1 76 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 240 2 1 114 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 228 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 240))))))))))))) (allB_succ' 14 227 240 (Eq.refl Bool.true) (allA_succ_of_accept 13 227 240 (accept_3_4
  13 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 227 240 (Polychromatic418967fa.accept_19_11_18_12_1_4802 11 227 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 240 (accept_3_4 10 227 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 240 (Polychromatic418967fa.accept_19_9_18_12_1_2286 9 227 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 240 (accept_3_4 7 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 227 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 240 (accept_3_4 4 227 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 227 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 240
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 240 (accept_3_4 1 227 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  240)))))))))))))) (allB_succ' 15 226 240 (Eq.refl Bool.true) (allA_succ_of_gcd 14 226 240 2 7 113 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 226 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 240 2 6 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 240 (accept_3_5 11 226 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 240 2 5 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 240 (Polychromatic418967fa.accept_22_9_6_20_1_8174 9 226 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 240 2 4 113 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 226 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 240 2 3 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 240 (accept_3_5 5 226 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 240 2 2 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 226 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 240 2 1 113 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 226 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 240))))))))))))))) (allB_succ' 16 225 240 (Eq.refl Bool.true) (allA_succ_of_gcd 15 225 240 15 1 15 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 225 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 225 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 240 3 4 75 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006
  11 225 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 225 240 5 2 45 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 225 240 3 3 75 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 240
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 225 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 225 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 240 3 2 75 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 225 240 5 1 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 240 (Polychromatic418967fa.accept_19_4_16_12_1_485 4 225 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 240 3 1 75 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 240
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 225 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 240 (Polychromatic418967fa.accept_18_1_9_6_1_6630 1 225 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 240)))))))))))))))) (allB_succ' 17 224 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 224 240 16 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 224 240 (Polychromatic418967fa.accept_21_15_14_9_1_2540 15 224 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 224 240 2 7 112 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 224 240 (accept_3_4 13 224 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 224 240 4 3 56 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 224 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 224 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 224 240 2 5 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 224 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 224 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 240 8 1 28 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 240 (accept_3_4 7 224 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 240 2 3 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 224 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 240 4 1 56 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 224 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 240 2 1 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 240 (accept_3_4 1 224 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  240))))))))))))))))) (allB_succ' 18 223 240 (Eq.refl Bool.true) (allA_succ_of_accept 17 223 240 (accept_3_5 17 223 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 240
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 16 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 240 (accept_3_5 14 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 223 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 240 (accept_3_5 11 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 240 (accept_3_5 8 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 240 (Polychromatic418967fa.accept_19_7_14_12_1_2261 7 223 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 240 (accept_3_5 5 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 223 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 240 (accept_3_5 2 223 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 223 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 240)))))))))))))))))) (allB_succ' 19 222 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 222 240 6 3 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 222 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 222 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 240 2 8 111 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 222 240 3 5 74 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 222 240 2 7 111 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 240
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 222 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 240 6 2 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 222 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 222 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 240 2 5 111 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 222 240 3 3 74 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 240 2 4 111 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 222 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 240 6 1 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 240 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 222 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 240 2 2 111 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 222 240 3 1 74 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 240 2 1 111 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 240
  (Polychromatic418967fa.accept_19_1_13_12_1_7748 1 222 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 240))))))))))))))))))) (allB_succ' 20 221 240 (Eq.refl Bool.true) (allA_succ_of_accept 19 221 240
  (accept_3_4 19 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 240
  (Polychromatic418967fa.accept_21_18_11_9_1_6956 18 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 221 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 240 (accept_3_4 16 221 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 15 221 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 240
  (Polychromatic418967fa.accept_22_14_1_20_1_11406 14 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 221 240 (accept_3_4 13 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 221 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 221 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 221 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 240 (accept_3_4 10 221 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 240 (Polychromatic418967fa.accept_14_9_11_2_1_2501
  9 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 240 (accept_3_4 7 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 221 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 240 (accept_3_4 4 221 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 221 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 240 (accept_3_4 1 221 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  240)))))))))))))))))))) (allB_succ' 21 220 240 (Eq.refl Bool.true) (allA_succ_of_gcd 20 220 240 20 1 11 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 220 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 240 2 9 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 240 (accept_3_5 17 220 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 240 4 4 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 220 240 5 3 44 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 220 240 2 7 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 220 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 220 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 220 240 4 3 55 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 220 240 (accept_3_5 11 220 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 240 10 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 240 (Polychromatic418967fa.accept_23_9_13_10_1_7898
  9 220 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 240 4 2 55 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 220 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 240 2 3 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 220 240 5 1 44 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 220 240 4 1 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 220 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 220 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 240 2 1 110 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 220 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 240))))))))))))))))))))) (allB_succ' 22 219 240 (Eq.refl Bool.true) (allA_succ_of_gcd 21 219 240 3 7 73
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 219 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 219 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 240 3 6 73 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 219 240 3 5 73 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 219 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 219 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 219 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 240 3 4 73 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 219 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 240 3 3 73 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 219 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 219 240 3 2 73 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 219 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 219 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 219 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 240 3 1 73 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 219 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 219 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 240)))))))))))))))))))))) (allB_succ' 23 218 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 218 240 2 11 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 218 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 218 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 218 240 2 10 109 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 218 240 (accept_3_4 19 218 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 218 240 2 9 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 218 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  218 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 240 2 8 109 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 240 2 7 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 240 (accept_3_4 13 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 240 2 6 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 240 (Polychromatic418967fa.accept_27_11_2_24_1_14474 11 218 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 240 2 5 109 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 240 2 4 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 240 (accept_3_4 7 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 240 2 3 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 218 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 240 2 2 109 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 240 2 1 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 240 (accept_3_4 1 218 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  240))))))))))))))))))))))) (allB_succ' 24 217 240 (Eq.refl Bool.true) (allA_succ_of_accept 23 217 240 (accept_3_5 23
  217 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 217 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 217 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 240 (accept_3_5 20 217 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 217 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 19 217 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 240
  (Polychromatic418967fa.accept_17_1_13_2_1_7086 18 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 240 (accept_3_5 17 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 217 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 240 (accept_3_5 14 217 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 217 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 240 (accept_3_5 11 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 217 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 240 (accept_3_5 8 217 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 217 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 240
  (Polychromatic418967fa.accept_17_6_13_2_1_4549 6 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 240 (accept_3_5 5 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 217 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 217 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 240 (accept_3_5 2 217 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 217 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 240)))))))))))))))))))))))) (allB_succ' 25 216 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 216 240 24 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 216 240 (Polychromatic418967fa.accept_17_6_12_2_1_10966 23 216 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 240 2 11 108 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 216 240 3 7 72 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 216 240 4 5 54 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 240
  (Polychromatic418967fa.accept_23_19_9_10_1_14332 19 216 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 216 240 6 3 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 216 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 216 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 240 8 2 27 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 216 240 3 5 72 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 216 240 2 7 108 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 240
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 216 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 240 12 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 216 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 216 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 240 2 5 108 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 216 240 3 3 72 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 216 240 8 1 27 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 240
  (Polychromatic418967fa.accept_17_7_12_2_1_7105 7 216 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 240 6 1 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 216 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 240 4 1 54 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 216 240 3 1 72 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 240 2 1 108 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  216 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 240)))))))))))))))))))))))))
  (allB_succ' 26 215 240 (Eq.refl Bool.true) (allA_succ_of_gcd 25 215 240 5 5 43 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 215 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 215 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 240 (accept_3_4 22 215 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 215 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 215 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 215 240 5 4 43 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 215 240 (accept_3_4 19 215 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 215 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 240 (accept_3_4 16 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  215 240 5 3 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 215 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 215 240 (accept_3_4 13 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 215 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 215 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 215 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 215 240 5 2 43 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 215 240
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 215 240 (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 215 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 240 (accept_3_4 7 215 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 215 240 (Polychromatic418967fa.accept_27_6_26_24_1_14473 6 215 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 215 240 5 1 43 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 215 240 (accept_3_4 4 215 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 215 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 240 (accept_3_4 1 215 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  240)))))))))))))))))))))))))) (allB_succ' 27 214 240 (Eq.refl Bool.true) (allA_succ_of_gcd 26 214 240 2 13 107 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 240
  (Polychromatic418967fa.accept_17_8_10_2_1_4546 25 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 240 2 12 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 240 (accept_3_5 23 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 240 2 11 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 214 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 240 2 10 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 240 2 9 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 240 (accept_3_5 17 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 240 2 8 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 240 (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 214 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 240 2 7 107 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 240 2 6 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 240 (accept_3_5 11 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 240 2 5 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 214 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 240 2 4 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 240 2 3 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 240 (accept_3_5 5 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 240 2 2 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 214 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 240 2 1 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 214 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 240))))))))))))))))))))))))))) (allB_succ' 28 213 240 (Eq.refl Bool.true) (allA_succ_of_gcd 27 213 240 3
  9 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213
  240 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 213 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 213 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 213 240 3 8 71 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 213 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 213 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 240 3 7 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 213 240 3 6 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 213 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 213 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 213
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 213 240 3 5 71 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 213 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 240 3 4 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 240 (Polychromatic418967fa.accept_13_11_5_6_1_519
  11 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 213 240 3 3 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 213 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 213 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 240 (Polychromatic418967fa.accept_17_7_9_2_1_629 7 213 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 240 3 2 71 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 213 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 240 3 1 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 213 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 213 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 213 240)))))))))))))))))))))))))))) (allB_succ' 29 212 240 (Eq.refl Bool.true) (allA_succ_of_gcd 28 212 240
  4 7 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212
  240 (Polychromatic418967fa.accept_17_10_8_2_1_8411 27 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 212 240 2 13 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 212 240 (accept_3_4 25 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 240 4 6 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 212 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 212 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 240 2 11 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  212 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 240 4 5 53 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 240 (accept_3_4 19
  212 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 240 2 9 106 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 212 240 4 4 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 212 240 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 212 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 212 240 2 7 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 212 240 (accept_3_4 13 212 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 212 240 4 3 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 212 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 212 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 240 2 5 106 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 240 4 2 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 212 240 (accept_3_4 7 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212
  240 2 3 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  212 240 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 212 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 212 240 4 1 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 212 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 212 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 240 2 1 106 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 240 (accept_3_4 1 212 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 212 240))))))))))))))))))))))))))))) (allB_succ' 30 211 240 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 211 240 (accept_3_5 29 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 211 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 211 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 211 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 240 (accept_3_5 26 211 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 240 (Polychromatic418967fa.accept_9_7_4_6_1_273
  25 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 240 (accept_3_5 23 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 240 (accept_3_5 20 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 211 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 240 (accept_3_5 17 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 211 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 240 (accept_3_5 14 211 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 211 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 240 (accept_3_5 11 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 240 (accept_3_5 8 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 211 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 240 (accept_3_5 5 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 211 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 240 (accept_3_5 2 211 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 211 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 240)))))))))))))))))))))))))))))) (allB_succ' 31 210
  240 (Eq.refl Bool.true) (allA_succ_of_gcd 30 210 240 30 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 210 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 210 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 240 2 14 105 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 210 240 3 9 70 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 210 240 2 13 105 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 210 240 5 5 42 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 210 240 6 4 35 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 210 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 240 2 11 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 210 240 3 7 70 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 210 240 10 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 210 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 210 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 240 6 3 35 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 210 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 240 2 8 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 210 240 15 1 14 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 240 2 7 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 210 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 240 6 2 35 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 210 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 240 10 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 210 240 3 3 70 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 210 240 2 4 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 210 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 210 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 240 6 1 35 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 210 240 5 1 42 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 210 240 2 2 105 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 240 3 1 70 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 240 2 1 105 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 210 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 240))))))))))))))))))))))))))))))) (allB_succ' 32 209 240 (Eq.refl Bool.true) (allA_succ_of_accept 31
  209 240 (accept_3_4 31 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 209 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 209 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 240 (accept_3_4 28 209 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 209 240 (Polychromatic418967fa.accept_21_6_20_9_1_6943 27 209 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 240 (accept_3_4 25 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 240 (accept_3_4 22 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 209 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 240
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 240 (accept_3_4 19 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 240 (accept_3_4 16 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 209 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 240 (accept_3_4 13 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 240 (accept_3_4 10 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 209 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 240 (accept_3_4 7 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 240 (Polychromatic418967fa.accept_21_6_20_9_1_6943 6 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 240 (accept_3_4 4 209 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 209 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 240
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 240 (accept_3_4 1 209 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  240)))))))))))))))))))))))))))))))) (allB_succ' 33 208 240 (Eq.refl Bool.true) (allA_succ_of_gcd 32 208 240 16 2 13 15
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 208 240 2 15 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 208 240 (accept_3_5 29 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 208 240 4 7 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 208 240 (Polychromatic418967fa.accept_28_27_12_16_1_14472 27 208 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 208 240 2 13 104 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 208 240 8 3 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 208 240 (accept_3_5 23 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  208 240 2 11 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 208 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 208 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 240 4 5 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 240 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  19 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 208 240 2 9 104 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 208 240
  (accept_3_5 17 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 208 240 16 1 13 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 208 240
  (Polychromatic418967fa.accept_17_15_4_2_1_8419 15 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 208 240 2 7 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 208 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 208 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 208 240 4 3 52 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 240 (accept_3_5 11 208 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 240 2 5 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 240 (Polychromatic418967fa.accept_17_9_4_2_1_2298 9
  208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 240 8 1 26 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 208 240 2 3 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 208 240 (accept_3_5 5 208 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 208 240 4 1 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 208 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 208 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 240 2 1 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 1
  208 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208
  240))))))))))))))))))))))))))))))))) (allB_succ' 34 207 240 (Eq.refl Bool.true) (allA_succ_of_gcd 33 207 240 3 11 69
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 207 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 32 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 240 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 207 240 3 10 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 207 240
  (Polychromatic418967fa.accept_19_10_17_12_1_2271 29 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 207 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 207 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 207 240 3 9 69 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 240 (Polychromatic418967fa.accept_18_7_9_6_1_4023 25 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 240 3 8 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 240 (Polychromatic418967fa.accept_13_10_12_6_1_991
  23 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 240
  (Polychromatic418967fa.accept_17_5_3_2_1_5847 22 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 207 240 3 7 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 207 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 207 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 240 3 6 69 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 240
  (Polychromatic418967fa.accept_21_17_18_9_1_9968 17 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 240 (Polychromatic418967fa.accept_25_16_7_15_1_14471 16 207 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 240 3 5 69 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 240
  (Polychromatic418967fa.accept_17_14_3_2_1_5848 14 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 240 3 4 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 240 (Polychromatic418967fa.accept_17_11_3_2_1_5867
  11 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 240
  (Polychromatic418967fa.accept_13_10_12_6_1_991 10 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 207 240 3 3 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 207 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 8 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 207
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 240 3 2 69 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 240 (Polychromatic418967fa.accept_21_4_18_9_1_6899 4 207 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 240 3 1 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 207 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 240
  (Polychromatic418967fa.accept_17_1_3_2_1_5846 1 207 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 240)))))))))))))))))))))))))))))))))) (allB_succ' 35 206 240 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  206 240 2 17 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 206 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 206 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 206 240 2 16 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 206 240 (accept_3_4 31 206 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 206 240 2 15 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 206 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 206 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 240 2 14 103 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 240 2 13 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 240 (accept_3_4 25 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 240 2 12 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 206 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 240 2 11 103 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 240 2 10 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 240 (accept_3_4 19 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 240 2 9 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 206 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 240 2 8 103 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 240 2 7 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 240 (accept_3_4 13 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 240 2 6 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 206 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 240 2 5 103 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 240 2 4 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 240 (accept_3_4 7 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 240 2 3 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 206 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 240 2 2 103 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 240 2 1 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 240 (accept_3_4 1 206 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  240))))))))))))))))))))))))))))))))))) (allB_succ' 36 205 240 (Eq.refl Bool.true) (allA_succ_of_gcd 35 205 240 5 7 41
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 205 240
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 34 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 240 (Polychromatic418967fa.accept_17_16_1_2_1_3403 33 205 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 240 (accept_3_5 32 205 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 205 240 5 6 41 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 205 240 (accept_3_5 29
  205 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 28 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 205 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 205 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 240 (accept_3_5 26 205 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 205 240 5 5 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 205 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 205 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 240 (accept_3_5 23 205 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 205 240 5 4 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 205 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 205 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 205
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 240 (accept_3_5 17 205
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 205 240 5 3 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 205 240 (accept_3_5 14 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 205 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 240 (accept_3_5 11 205 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 205 240 5 2 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 205 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 240 (accept_3_5 8 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489
  7 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 240
  (Polychromatic418967fa.accept_17_6_1_2_1_10823 6 205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 205 240 5 1 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 205 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 205 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 240 (accept_3_5 2 205 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  205 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  240)))))))))))))))))))))))))))))))))))) (allB_succ' 37 204 240 (Eq.refl Bool.true) (allA_succ_of_gcd 36 204 240 12 3
  17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 240
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 35 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 204 240 2 17 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 204 240 3 11 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 240 4 8 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 204 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 240 6 5 34 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 240
  (Polychromatic418967fa.accept_13_3_9_6_1_502 29 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 240 4 7 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 204 240 3 9 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 204 240 2 13 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 204 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 240 12 2 17 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 240
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 204 240 2 11 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 204 240 3 7 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 204 240 4 5 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 204 240 (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 204 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 240 6 3 34 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 204 240 4 4 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 204 240 3 5 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 204 240 2 7 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 204 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 240 12 1 17 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 240
  (Polychromatic418967fa.accept_21_11_15_9_1_3868 11 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 204 240 2 5 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 240 3 3 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 240 4 2 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 204 240 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 204 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 240 6 1 34 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 240
  (Polychromatic418967fa.accept_21_5_15_9_1_11534 5 204 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 240 4 1 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 204 240 3 1 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 204 240 2 1 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 204 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 240))))))))))))))))))))))))))))))))))))) (allB_succ' 38 203 240
  (Eq.refl Bool.true) (allA_succ_of_accept 37 203 240 (accept_3_4 37 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 203 240 (Polychromatic418967fa.accept_21_15_14_9_1_2540 36 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 240 (Polychromatic418967fa.accept_9_8_5_6_1_538
  35 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 240 (accept_3_4 34
  203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 33 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 203 240 (Polychromatic418967fa.accept_23_9_19_10_1_14340 32 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 240 (accept_3_4 31 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 203 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 240 (accept_3_4 28 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 240 (accept_3_4 25 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 203 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 240
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 240 (accept_3_4 22 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 240 (accept_3_4 19 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 203 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 240 (accept_3_4 16 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 240 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 203 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 240 (accept_3_4 13 203 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 203 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 240 (accept_3_4 10 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 240 (accept_3_4 7 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 240 (Polychromatic418967fa.accept_19_6_13_12_1_6220 6 203 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 240 (accept_3_4 4 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 203 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 240 (accept_3_4 1 203 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 240)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 202 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 202 240 2 19 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 202 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 202 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 202 240 2 18 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 202 240 (accept_3_5 35 202 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 202 240 2 17 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 202 240
  (Polychromatic418967fa.accept_18_15_4_6_1_1763 33 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 202 240 2 16 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 202 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 202 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 202 240 2 15 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 202 240 (accept_3_5 29 202 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 202 240 2 14 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 202 240 (Polychromatic418967fa.accept_13_1_7_6_1_142
  27 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 240 2 13 101 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 240 2 12 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 240 (accept_3_5 23 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 240 2 11 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 202 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 240 2 10 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 240 2 9 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 240 (accept_3_5 17 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 240 2 8 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 202 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 240 2 7 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 240
  (Polychromatic418967fa.accept_11_2_4_9_1_484 13 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 240 2 6 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 240 (accept_3_5 11 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 240 2 5 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 202 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 240 2 4 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 240 2 3 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 240 (accept_3_5 5 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 240 2 2 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 202 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 240 2 1 101 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 202 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 240))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 201 240 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 201 240 3 13 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 201 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 201 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 201 240 3 12 67 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 201 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 201 240 3 11 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 201 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 201 240 3 10 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 201 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 201 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 240 3 9 67 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 240 3 8 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 201 240 3 7 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 201 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 201 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 240 3 6 67 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 240 3 5 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 201 240 3 4 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 201 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 201 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 240 3 3 67 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 240 3 2 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 201 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 201 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 201 240 3 1 67 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 201 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 201 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 201 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 240))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 200 240 (Eq.refl Bool.true) (allA_succ_of_gcd 40 200 240 40 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 200 240 2 19 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 240 (accept_3_4 37 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 200 240 4 9 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 200 240 5 7 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 200 240 2 17 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 200 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 240 8 4 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 240 (accept_3_4 31 200 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 240 10 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 240 (Polychromatic418967fa.accept_11_7_2_9_1_480
  29 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 240 4 7 50 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 240 2 13 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 200 240 5 5 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 200 240 8 3 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 200 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 200 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 240 2 11 100 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 240 20 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 240 (accept_3_4 19 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 240 2 9 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 200 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 240 8 2 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 200 240 5 3 40 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 200 240 2 7 100 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 240 (accept_3_4 13 200 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 240 4 3 50 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 240
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 200 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 200 240 10 1 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 200 240 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 200 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 240 8 1 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 240 (accept_3_4 7 200 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 240 2 3 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 200 240 5 1 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 200 240 4 1 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 200 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 240 2 1 100 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 240 (accept_3_4 1
  200 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200 240)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 199 240 (Eq.refl Bool.true) (allA_succ_of_accept 41 199 240 (accept_3_5 41 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 199 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 199 240 (accept_3_5 38 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 199 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 199 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 240 (accept_3_5 35 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 199 240 (accept_3_5 32 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 199 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 199 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 240 (accept_3_5 29 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 240 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 240 (accept_3_5 26 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 240 (accept_3_5 23 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 199 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 240 (accept_3_5 20 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 240 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 240 (accept_3_5 17 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 199 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 240 (accept_3_5 14 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 240 (accept_3_5 11 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 199 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 240 (accept_3_5 8 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 240 (accept_3_5 5 199 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 199 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 240 (accept_3_5 2 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 199 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 240)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 198 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 198 240 6 7 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 198 240 (Polychromatic418967fa.accept_23_18_14_10_1_7900 41 198 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 240 2 20 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 198 240 3 13 66 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 198 240 2 19 99 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 240
  (Polychromatic418967fa.accept_17_3_11_2_1_8435 37 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 240 6 6 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 198 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 198 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 240 2 17 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 240 3 11 66 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 240 2 16 99 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 240
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 240 6 5 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 198 240 (Polychromatic418967fa.accept_19_10_8_12_1_7733 29 198 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 240 2 14 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 240 3 9 66 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 240 2 13 99 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 240
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 25 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 240 6 4 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 198 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 240 2 11 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 240 3 7 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 240 2 10 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 240
  (Polychromatic418967fa.accept_23_19_14_10_1_12916 19 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 198 240 6 3 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 198 240 (Polychromatic418967fa.accept_25_17_23_15_1_14432 17 198 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 240 2 8 99 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 240 3 5 66 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 240 2 7 99 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 240
  (Polychromatic418967fa.accept_23_13_14_10_1_14470 13 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 198 240 6 2 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 198 240 (Polychromatic418967fa.accept_19_11_8_12_1_6204 11 198 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 240 2 5 99 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 240 3 3 66 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 240 2 4 99 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 240
  (Polychromatic418967fa.accept_19_7_8_12_1_9107 7 198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 240 6 1 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 198 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 240 2 2 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 240 3 1 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 198 240 2 1 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 1
  198 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  240))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 197 240 (Eq.refl Bool.true) (allA_succ_of_accept 43 197
  240 (accept_3_4 43 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 240
  (Polychromatic418967fa.accept_17_8_10_2_1_4546 42 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 197 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 197 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 240 (accept_3_4 40 197 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 197 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 240 (Polychromatic418967fa.accept_7_3_1_2_1_247
  38 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 240 (accept_3_4 37
  197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 197 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 35 197 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 240 (accept_3_4 34 197 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 197 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 197 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 240 (accept_3_4 31 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 240 (accept_3_4 28 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 197 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 240
  (Polychromatic418967fa.accept_22_4_21_20_1_14455 26 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 197 240 (accept_3_4 25 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 197 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 197 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 197 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 240 (accept_3_4 22 197 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 240 (accept_3_4 19 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 240 (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 240 (accept_3_4 16 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 240 (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 197 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 240 (accept_3_4 13 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 240 (accept_3_4 10 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 197 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 240 (accept_3_4 7 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 240 (accept_3_4 4 197 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 197 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 240 (accept_3_4 1 197 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  240)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 196 240 (Eq.refl Bool.true) (allA_succ_of_gcd 44 196
  240 4 11 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  196 240 (Polychromatic418967fa.accept_25_18_21_15_1_14469 43 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 196 240 2 21 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 196 240 (accept_3_5 41 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 196 240 4 10 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 196 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 196 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 196 240 2 19 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 196 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 196 240 4 9 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 196 240 (accept_3_5 35 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  196 240 2 17 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 196 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 196 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 240 4 8 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 240 2 15 98 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 240 (accept_3_5 29
  196 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 240 4 7 49 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 240
  (Polychromatic418967fa.accept_19_8_6_12_1_13105 27 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 196 240 2 13 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 196 240 (Polychromatic418967fa.accept_23_2_12_10_1_14468 25 196 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 240 4 6 49 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 240 (accept_3_5 23
  196 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 240 2 11 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 196 240 4 5 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 196 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 240 2 9 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 240 (accept_3_5 17 196 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 240 4 4 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 240 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 196
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 240 2 7 98 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 240 4 3 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 196 240 (accept_3_5 11 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  196 240 2 5 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 196 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 196 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 240 4 2 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 240 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 196 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 240 2 3 98 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 240 (accept_3_5 5
  196 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 240 4 1 49 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 196 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 196 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 196 240 2 1 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 196 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 196 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 196 240))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 195 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 195 240 15 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 195 240 (Polychromatic418967fa.accept_17_10_8_2_1_8411 44 195
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 195 240 3 14 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 195 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 195 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 195 240 5 8 39 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 195 240 3 13 65 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 195 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 240 (Polychromatic418967fa.accept_21_16_6_9_1_8464 37 195 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 240 3 12 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 195 240 5 7 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 240
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 34 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 195 240 3 11 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 195 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 195 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 195 240 15 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 195 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 195 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 240
  (Polychromatic418967fa.accept_17_11_8_2_1_3398 28 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 195 240 3 9 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 195 240 (Polychromatic418967fa.accept_19_7_5_12_1_7756 26 195 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 240 5 5 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 195 240 3 8 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999
  23 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 195 240 3 7 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 195 240 5 4 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 195 240 (Polychromatic418967fa.accept_26_19_13_6_1_14467 19 195 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 240 3 6 65 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 240 (Polychromatic418967fa.accept_17_16_8_2_1_5890 16 195 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 240 15 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 240
  (Polychromatic418967fa.accept_21_14_6_9_1_14343 14 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 240 (Polychromatic418967fa.accept_19_13_5_12_1_6107 13 195 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 240 3 4 65 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 195 240 5 2 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 195 240 3 3 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 195 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 195 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 240 (Polychromatic418967fa.accept_19_7_5_12_1_7756 7 195
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 240 3 2 65 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 195 240 5 1 39 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 195 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 240 3 1 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 240 (Polychromatic418967fa.accept_21_2_6_9_1_5355 2 195 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 195 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  240)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 194 240 (Eq.refl Bool.true) (allA_succ_of_gcd 46 194
  240 2 23 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 194 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 194 240 2 22 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 194 240 (accept_3_4 43 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 240 2 21 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 194 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 240 2 20 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 240 2 19 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 240 (accept_3_4 37 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 240 2 18 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 194 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 240 2 17 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 240 2 16 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 240 (accept_3_4 31 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 240 2 15 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 194 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 240 2 14 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 240
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 240 2 13 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 240 (accept_3_4 25 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 240 2 12 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 240 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 194 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 240 2 11 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 240 2 10 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 240 (accept_3_4 19 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 240 2 9 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 194 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 240 2 8 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 240
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 240 2 7 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 240 (accept_3_4 13 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 240 2 6 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 194 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 240 2 5 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 240
  (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 240 2 4 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 240 (accept_3_4 7 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  240 2 3 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 194 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 240 2 2 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 194 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 240 2 1 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 240 (accept_3_4 1 194 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 240))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 193 240 (Eq.refl Bool.true) (allA_succ_of_accept 47 193 240 (accept_3_5 47 193 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 193 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 193 240 (Polychromatic418967fa.accept_18_9_13_6_1_877
  45 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 240 (accept_3_5 44
  193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 193 240 (Polychromatic418967fa.accept_23_19_9_10_1_14332 42 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 240 (accept_3_5 41 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 193 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 193 240 (accept_3_5 38 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 193 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 193 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 240 (accept_3_5 35 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 193 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 193 240 (accept_3_5 32 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 193 240 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 240 (accept_3_5 29 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 240 (accept_3_5 26 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 240 (Polychromatic418967fa.accept_23_1_9_10_1_14466 24 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 240 (accept_3_5 23 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 240 (Polychromatic418967fa.accept_23_22_9_10_1_14465 22
  193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 240 (accept_3_5 20 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 240 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 240 (accept_3_5 17 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 193 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 240
  (Polychromatic418967fa.accept_19_15_3_12_1_11789 15 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 193 240 (accept_3_5 14 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 193 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 193 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 193 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 240 (accept_3_5 11 193 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 240 (accept_3_5 8 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 240 (accept_3_5 5 193 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 193 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 240 (accept_3_5 2 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 193 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 240)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 192 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 192 240 48 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 192 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 240 2 23 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 192 240 3 15 64 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 192 240 4 11 48 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 240 6 7 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 192 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 192 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 240 8 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 192 240 3 13 64 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 192 240 2 19 96 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 240 12 3 16 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 192 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 240 2 17 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 192 240 3 11 64 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 240 16 2 12 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 240 6 5 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 192 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 192 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 240 4 7 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 192 240 3 9 64 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 192 240 2 13 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 240 24 1 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 192 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 240 2 11 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 240 3 7 64 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 240 4 5 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 240 6 3 32 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 240 16 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 192 240 3 5 64 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 192 240 2 7 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 192 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 192 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 240 12 1 16 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 240 2 5 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 192 240 3 3 64 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 192 240 8 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 192 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 192 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 240 6 1 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5
  192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 240 4 1 48 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 240 3 1 64 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 240 2 1 96 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 192 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 240))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 191 240 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 191 240 (accept_3_4 49 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 240 (Polychromatic418967fa.accept_19_9_1_12_1_6234 47 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 240 (accept_3_4 46 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 240 (Polychromatic418967fa.accept_19_7_1_12_1_6134 45 191
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 240 (accept_3_4 43 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 240 (Polychromatic418967fa.accept_13_3_9_6_1_502 42 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 240 (accept_3_4 40 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 240
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 38 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 240 (accept_3_4 37 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 240 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 240 (accept_3_4 34 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 240 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 240 (accept_3_4 31 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 240 (Polychromatic418967fa.accept_13_3_9_6_1_502 29 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 240 (accept_3_4 28 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 191
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 240 (accept_3_4 25 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 240 (accept_3_4 22 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 240
  (Polychromatic418967fa.accept_13_7_9_6_1_148 20 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 240 (accept_3_4 19 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 240 (accept_3_4 16 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 240 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 240 (accept_3_4 13 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 240 (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 240 (accept_3_4 10 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 240 (Polychromatic418967fa.accept_17_9_4_2_1_2298 9 191 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 240 (accept_3_4 7 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 240 (Polychromatic418967fa.accept_17_6_4_2_1_5889 6 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 240 (accept_3_4 4 191 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 191 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 240
  (Polychromatic418967fa.accept_11_2_4_9_1_484 2 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 240 (accept_3_4 1 191 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  240)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 190 240 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  190 240 10 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 190 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 190 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 190 240 2 24 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 190 240 (accept_3_5 47 190 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 190 240 2 23 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 190 240 5 9 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 190 240 2 22 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 43
  190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 190 240 2 21 95 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 190 240 (accept_3_5 41
  190 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 190 240 10 4 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 190 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 190 240 2 19 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 190 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 190 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 190 240 2 18 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 190 240 5 7 38 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 190 240 2 17 95 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 190 240
  (Polychromatic418967fa.accept_18_15_10_6_1_1781 33 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 190 240 2 16 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 190 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 190 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 240 10 3 19 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 240 (accept_3_5 29 190 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 190 240 2 14 95 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 190 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 190 240 2 13 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 190 240 5 5 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 190 240 2 12 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 190 240 (accept_3_5 23 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 240 2 11 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 190 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 240 10 2 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 240
  (Polychromatic418967fa.accept_23_19_6_10_1_14443 19 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 190 240 2 9 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 190 240 (accept_3_5 17 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 240 2 8 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 190 240 5 3 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 190 240 2 7 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 190 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 190 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 190 240 2 6 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 190 240 (accept_3_5 11 190 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 240 10 1 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 240
  (Polychromatic418967fa.accept_22_9_14_20_1_12933 9 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 190 240 2 4 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 190 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 190 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 190 240 2 3 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 190 240 5 1 38 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 190 240 2 2 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 190 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 190 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 190 240 2 1 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 190 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 190 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 190 240))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52
  189 240 (Eq.refl Bool.true) (allA_succ_of_gcd 51 189 240 3 17 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 189 240 (Polychromatic418967fa.accept_18_14_9_6_1_1777 50 189
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 49 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 189 240 3 16 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 189 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 47 189 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 240
  (Polychromatic418967fa.accept_25_21_14_15_1_14395 46 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 189 240 3 15 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 189 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 44 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 240
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 189 240 3 14 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 189 240 (Polychromatic418967fa.accept_23_18_5_10_1_11274 41 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 40 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 189 240 3 13 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 189 240 (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 240
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 189 240 3 12 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 189 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 240
  (Polychromatic418967fa.accept_19_15_18_12_1_6180 34 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 189 240 3 11 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 189 240 (Polychromatic418967fa.accept_18_14_9_6_1_1777 32 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 189 240 3 10 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 189 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 189 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 240
  (Polychromatic418967fa.accept_19_9_18_12_1_2286 28 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 189 240 3 9 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 189 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 240
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 189 240 3 8 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 189 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 189 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 189
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 240 3 7 63 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 240
  (Polychromatic418967fa.accept_18_2_9_6_1_4025 20 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 19 189 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 240 3 6 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 240 (Polychromatic418967fa.accept_13_4_7_6_1_2359
  17 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 240
  (Polychromatic418967fa.accept_23_16_5_10_1_14464 16 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 189 240 3 5 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 189 240 (Polychromatic418967fa.accept_13_1_7_6_1_142 14 189 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 240 3 4 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 240 (Polychromatic418967fa.accept_19_11_18_12_1_4802 11 189 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 240
  (Polychromatic418967fa.accept_25_10_14_15_1_14463 10 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 189 240 3 3 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 189 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 8 189 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 240 3 2 63 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 240 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 189 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 240 3 1 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025 2 189 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 240
  (Polychromatic418967fa.accept_13_1_7_6_1_142 1 189 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 240)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 188 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 188 240 4 13 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 188 240 (Polychromatic418967fa.accept_28_23_20_16_1_14462 51 188 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 188 240 2 25 94 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 188 240 (accept_3_4 49 188 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 188 240 4 12 47 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 188 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 188 240 2 23 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 188 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 188 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 188 240 4 11 47 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 188 240 (accept_3_4 43 188 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 188 240 2 21 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 188 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 240 4 10 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 240 2 19 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 240 (accept_3_4 37 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 240 4 9 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 240 (Polychromatic418967fa.accept_21_14_20_9_1_5306 35 188 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 240 2 17 94 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 240
  (Polychromatic418967fa.accept_17_16_1_2_1_3403 33 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 240 4 8 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 188 240 (accept_3_4 31 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  188 240 2 15 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 188 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 188 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 240 4 7 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 240 (Polychromatic418967fa.accept_18_9_8_6_1_4021
  27 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 240 2 13 94 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 240
  (accept_3_4 25 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 240 4 6 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 188 240 2 11 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 188 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 188 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 240 4 5 47 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 240 (accept_3_4 19 188 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 240 2 9 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 240 4 4 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 240 2 7 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 240 (accept_3_4 13 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 240 4 3 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 188 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 188 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 240 2 5 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 240 (Polychromatic418967fa.accept_18_9_8_6_1_4021 9
  188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 240 4 2 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 240 (accept_3_4 7
  188 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 240 2 3 94 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 188 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 188 240 4 1 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 188 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 188 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 240 2 1 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 240 (accept_3_4 1 188 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 240))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 187 240
  (Eq.refl Bool.true) (allA_succ_of_accept 53 187 240 (accept_3_5 53 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 187 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 187 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 187
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 240 (accept_3_5 50 187
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 187 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 240 (accept_3_5 47 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 187 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 240 (accept_3_5 44
  187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 240
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 43 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 187 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 240 (accept_3_5 41 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 187 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 240 (Polychromatic418967fa.accept_7_4_5_2_1_243
  39 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 240 (accept_3_5 38
  187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 187 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 240 (accept_3_5 35 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 187 240 (Polychromatic418967fa.accept_19_15_16_12_1_4779 34 187 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 240
  (Polychromatic418967fa.accept_19_14_16_12_1_13098 33 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 187 240 (accept_3_5 32 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 187 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 187 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 240 (accept_3_5 29 187 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 240
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 240 (accept_3_5 26 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 240 (accept_3_5 23 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 187 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 240 (accept_3_5 20 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 240 (accept_3_5 17 187 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 187 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 240
  (Polychromatic418967fa.accept_19_15_16_12_1_4779 15 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 187 240 (accept_3_5 14 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 187 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 187 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 187 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 240 (accept_3_5 11 187 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 10
  187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 9 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 240 (accept_3_5 8 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 240 (Polychromatic418967fa.accept_19_6_16_12_1_6118 6 187 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 240 (accept_3_5 5 187 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 187 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 240 (accept_3_5 2 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 187 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 240)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 186 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 186 240 6 9 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 240 (Polychromatic418967fa.accept_21_11_18_9_1_465 53 186 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 240 2 26 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 186 240 3 17 62 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 186 240 2 25 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 240
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 240 6 8 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 186 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 186 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 240 2 23 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 186 240 3 15 62 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 186 240 2 22 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 240
  (Polychromatic418967fa.accept_19_5_15_12_1_6273 43 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 186 240 6 7 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 186 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 186 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 240 2 20 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 186 240 3 13 62 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 240 2 19 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 240
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 240 6 6 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 186 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 186 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 240 2 17 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 186 240 3 11 62 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 186 240 2 16 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 240
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 240 6 5 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 240 (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 186 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 240 2 14 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 186 240 3 9 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 186 240 2 13 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 240
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 25 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 186 240 6 4 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 186 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 186 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 240 2 11 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 240 3 7 62 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 240 2 10 93 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 240 6 3 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 240 (Polychromatic418967fa.accept_19_17_15_12_1_10534 17 186 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 240 2 8 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 240 3 5 62 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 240 2 7 93 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 240 6 2 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 186 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 240 2 5 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 240 3 3 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 240 2 4 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7
  186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 240 6 1 31 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 186 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 240 2 2 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 186 240 3 1 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 186 240 2 1 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 186 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 240))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 185 240 (Eq.refl Bool.true) (allA_succ_of_gcd 55 185 240 5 11 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 185 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 54
  185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 240 (accept_3_4 52 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 51 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 185 240 5 10 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 185 240 (accept_3_4 49 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 185 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 240 (accept_3_4 46 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 185 240 5 9 37 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 185 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 240 (accept_3_4 43 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 240 (Polychromatic418967fa.accept_26_16_3_6_1_14461 42 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 185 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 185 240 5 8 37 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 185 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 185 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 240 (accept_3_4 37 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 185 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 185 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 185 240 5 7 37 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 185 240 (accept_3_4 34 185 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 240
  (Polychromatic418967fa.accept_19_13_14_12_1_4797 32 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 185 240 (accept_3_4 31 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 185 240 5 6 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 185 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 240 (accept_3_4 28 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 185 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 185 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  26 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 185 240 5 5 37 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 185 240
  (Polychromatic418967fa.accept_17_7_15_2_1_10843 24 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 185 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 240 (accept_3_4 22 185 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 185 240 5 4 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 185 240 (accept_3_4 19
  185 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 240
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 185 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 240 (accept_3_4 16 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 185 240 5 3 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 185 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 185 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 240 (accept_3_4 13 185 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 185 240 5 2 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 185 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 240 (accept_3_4 7 185 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 240 5 1 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 240 (accept_3_4 4
  185 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 185 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 240 (accept_3_4 1 185 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 184 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 184 240 8 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 184 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 184 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 240 2 27 92 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 240 (accept_3_5 53 184 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 240 4 13 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 240 (Polychromatic418967fa.accept_13_12_2_6_1_2396
  51 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 240 2 25 92 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 184 240 8 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 184 240 (accept_3_5 47 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  184 240 2 23 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 184 240 (Polychromatic418967fa.accept_21_3_16_9_1_8528 45 184 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 240 4 11 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 43
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 240 2 21 92 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 240 (accept_3_5 41
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 240 8 5 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 184 240 2 19 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 184 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 184 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 240 4 9 46 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 240 (accept_3_5 35 184 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 240 2 17 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 240
  (Polychromatic418967fa.accept_17_16_14_2_1_5841 33 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 184 240 8 4 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 184 240 (Polychromatic418967fa.accept_21_10_16_9_1_5302 31 184 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 240 2 15 92 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 240 (accept_3_5 29
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 240 4 7 46 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 240
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 184 240 2 13 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 184 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 184 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 240 8 3 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 240 (accept_3_5 23 184 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 240 2 11 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 240 4 5 46 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 240 2 9 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 240 (accept_3_5 17 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 240 8 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 184 240 (Polychromatic418967fa.accept_18_15_4_6_1_1763 15 184 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 240 2 7 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 240
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 184 240 4 3 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 184 240 (accept_3_5 11 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 240 2 5 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 240 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 184 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 240 8 1 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 240 2 3 92 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 240 (accept_3_5 5
  184 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 240 4 1 46 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 184 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 184 240 2 1 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 184 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 184 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 184 240))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  58 183 240 (Eq.refl Bool.true) (allA_succ_of_gcd 57 183 240 3 19 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 183 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 183 240 3 18 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 183 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 183 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 240 (Polychromatic418967fa.accept_7_3_1_2_1_247
  52 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 183 240 3 17 61 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 183 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 183 240 3 16 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 183 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 240 3 15 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 183 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 240 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 183 240 3 14 61 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 183 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 240 3 13 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 240 3 12 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 183 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  34 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 183 240 3 11 61 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 183 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 240 3 10 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 240 3 9 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 183 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 240 3 8 61 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 240 3 7 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 240 3 6 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 183 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 240 3 5 61 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 240 3 4 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 240 3 3 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 240 3 2 61 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 183 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 240 3 1 61 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 183 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 182 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 182 240 2 29 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 182 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 182 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 182 240 2 28 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 182 240 (accept_3_4 55 182 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 182 240 2 27 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 182 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53
  182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 240 2 26 91 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 240
  (Polychromatic418967fa.accept_19_13_11_12_1_3447 51 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 182 240 2 25 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 182 240 (accept_3_4 49 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 240 2 24 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 182 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 240 2 23 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 240
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 45 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 240 2 22 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 240 (accept_3_4 43 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 240 2 21 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 182 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 240 2 20 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 240 2 19 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 240 (accept_3_4 37 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 240 2 18 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 182 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 240 2 17 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 240
  (Polychromatic418967fa.accept_22_11_6_20_1_14347 33 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 240 2 16 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 240 (accept_3_4 31 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 240 2 15 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 240 (Polychromatic418967fa.accept_19_10_11_12_1_6114 29 182 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 240 2 14 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 240
  (Polychromatic418967fa.accept_17_10_12_2_1_3385 27 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 182 240 2 13 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 182 240 (accept_3_4 25 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 240 2 12 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 182 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 240 2 11 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 240 2 10 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 240 (accept_3_4 19 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 240 2 9 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 182 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 240 2 8 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 240
  (Polychromatic418967fa.accept_21_15_14_9_1_2540 15 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 240 2 7 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 240 (accept_3_4 13 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 240 2 6 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 240 (Polychromatic418967fa.accept_22_11_6_20_1_14347 11 182 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 240 2 5 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 240
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 9 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 240 2 4 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 240 (accept_3_4 7 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  240 2 3 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 182 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 240 2 2 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 240 2 1 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 240 (accept_3_4 1 182 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 181 240 (Eq.refl Bool.true) (allA_succ_of_accept 59 181 240 (accept_3_5 59 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 240 (accept_3_5 56 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 240 (Polychromatic418967fa.accept_19_17_10_12_1_6157 55 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 181 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 240 (accept_3_5 53 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 52
  181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 240 (accept_3_5 50 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 240 (accept_3_5 47 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 240 (accept_3_5 44 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 240 (Polychromatic418967fa.accept_17_8_11_2_1_3415 42 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 240 (accept_3_5 41 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 240 (accept_3_5 38 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 240 (Polychromatic418967fa.accept_17_3_11_2_1_8435 37 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 240 (accept_3_5 35 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 240 (accept_3_5 32 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 240 (accept_3_5 29 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 240
  (Polychromatic418967fa.accept_18_9_1_6_1_5301 27 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 240 (accept_3_5 26 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 240 (accept_3_5 23 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 240 (accept_3_5 20 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 240 (Polychromatic418967fa.accept_23_19_20_10_1_14360 19 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 240 (accept_3_5 17 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 240 (accept_3_5 14 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 240 (accept_3_5 11 181 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 240
  (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 240 (accept_3_5 8 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 240 (Polychromatic418967fa.accept_19_6_10_12_1_11771 6 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 240 (accept_3_5 5 181 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 181 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 240 (accept_3_5 2 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 180 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 180 240 60 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 180 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 180 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 240 2 29 90 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 180 240 3 19 60 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 240 4 14 45 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 180 240 5 11 36
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 180 240 6 9 30
  40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 180 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 180 240 4 13 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 180 240 3 17 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 240 10 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 180
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 180 240 12 4 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 180 240
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 180 240 2 23 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 180 240 15 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 240 4 11 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 180
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 180 240 6 7 30 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 180 240
  (Polychromatic418967fa.accept_19_3_9_12_1_6253 41 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 240 20 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 180 240 3 13 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 180 240 2 19 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 180 240 (Polychromatic418967fa.accept_19_18_9_12_1_6153 37 180 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 240 12 3 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 180 240 5 7 36 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 240 2 17 90 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 240 3 11 60
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 240 4 8 45
  60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 240 30 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 240 (Polychromatic418967fa.accept_17_12_10_2_1_5835 29 180 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 240 4 7 45 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 240 3 9 60 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 240 2 13 90 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 180 240 5 5 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 180 240 12 2 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 240
  (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 240 2 11 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 180 240 3 7 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 180 240 20 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 180 240 (Polychromatic418967fa.accept_21_19_12_9_1_9957 19 180 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 240 6 3 30 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 240 4 4 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 180 240 15 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 180 240 2 7 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 180 240 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 180 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 240 12 1 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 240 10 1 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 180 240 3 3 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 180 240 4 2 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 180 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 180 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 240 6 1 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 240 5 1 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 240 4 1 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 240 3 1 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 240 2 1 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 240 (Polychromatic418967fa.accept_19_1_9_12_1_6207
  1 180 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 179 240 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 179 240 (accept_3_4 61 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 240 (Polychromatic418967fa.accept_21_18_11_9_1_6956 60 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 240 (accept_3_4 58 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 240 (accept_3_4 55 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 240 (Polychromatic418967fa.accept_19_15_8_12_1_1286 53 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 240 (accept_3_4 52 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 179
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 240 (accept_3_4 49 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 240 (accept_3_4 46 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 240 (Polychromatic418967fa.accept_17_11_9_2_1_8423 45 179 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 44 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 240 (accept_3_4 43 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 240 (accept_3_4 40 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 240 (accept_3_4 37 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 240 (Polychromatic418967fa.accept_21_15_11_9_1_2470 36 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 240 (accept_3_4 34 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 179 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 240 (accept_3_4 31 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 240 (accept_3_4 28 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 240 (accept_3_4 25 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 240 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 240 (accept_3_4 22 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 240 (accept_3_4 19 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 240 (accept_3_4 16 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 179
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 240 (accept_3_4 13 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 240 (accept_3_4 10 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 240
  (Polychromatic418967fa.accept_22_8_3_20_1_8170 8 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 240 (accept_3_4 7 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 240 (accept_3_4 4 179 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 179 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 240 (accept_3_4 1 179 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 178 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 178 240 2 31 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 178 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 178 240 2 30 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 178 240 (accept_3_5 59 178 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 178 240 2 29 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 178 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 57
  178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 240 2 28 89 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 240 2 27 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 240 (accept_3_5 53 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 240 2 26 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 240 2 25 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 240 2 24 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 240 (accept_3_5 47 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 240 2 23 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 240 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 178 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 240 2 22 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 240 2 21 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 240 (accept_3_5 41 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 240 2 20 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 240 2 19 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 240 2 18 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 240 (accept_3_5 35 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 240 2 17 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 240 2 16 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 240 2 15 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 240 (accept_3_5 29 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 240 2 14 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 240 2 13 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 240
  (Polychromatic418967fa.accept_22_3_2_20_1_14460 25 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 178 240 2 12 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 178 240 (accept_3_5 23 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 240 2 11 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 240 2 10 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 240 2 9 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 240 (accept_3_5 17 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 240 2 8 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 178 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 240 2 7 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 240 2 6 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 240 (accept_3_5 11 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 240 2 5 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 240 (Polychromatic418967fa.accept_25_9_3_15_1_11037 9 178 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 240 2 4 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 240
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 240 2 3 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 240 (accept_3_5 5 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  240 2 2 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 240 2 1 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 178 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 177 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 177 240 3 21 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 177 240 (Polychromatic418967fa.accept_22_18_1_20_1_12931 62 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 240
  (Polychromatic418967fa.accept_19_4_6_12_1_13144 61 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 177 240 3 20 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 177 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999 59 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 177 240 3 19 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 240 (Polychromatic418967fa.accept_19_18_6_12_1_6250 56 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 240
  (Polychromatic418967fa.accept_19_17_6_12_1_7757 55 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 177 240 3 18 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 177 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 53 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 240
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 52 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 177 240 3 17 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 177 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023 50 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 240
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 49 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 240 3 16 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 240 (Polychromatic418967fa.accept_17_13_7_2_1_4562 47 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 240
  (Polychromatic418967fa.accept_14_4_9_2_1_95 46 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 240 3 15 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 240 (Polychromatic418967fa.accept_27_17_15_24_1_14320 44 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 240
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 177 240 3 14 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 177 240 (Polychromatic418967fa.accept_13_2_8_6_1_2390 41 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 240
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 40 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 240 3 13 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 240 (Polychromatic418967fa.accept_25_13_2_15_1_14459 38 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 240
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 240 3 12 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 35 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 240
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 34 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 177 240 3 11 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 177 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 240
  (Polychromatic418967fa.accept_22_9_1_20_1_14458 31 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 177 240 3 10 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 177 240 (Polychromatic418967fa.accept_17_12_7_2_1_4561 29 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 240
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 177 240 3 9 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 177 240 (Polychromatic418967fa.accept_17_9_7_2_1_2347 26 177 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 240 (Polychromatic418967fa.accept_14_11_9_2_1_6382 25 177
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 240 3 8 59 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 240
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 240 (Polychromatic418967fa.accept_18_4_15_6_1_3994 22 177 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 240 3 7 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 240
  (Polychromatic418967fa.accept_25_20_2_15_1_14457 20 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 177 240 (Polychromatic418967fa.accept_22_19_1_20_1_4872 19 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 240 3 6 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 240
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 177 240 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 177 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 240 3 5 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 240
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 240 (Polychromatic418967fa.accept_17_13_7_2_1_4562 13 177 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 240 3 4 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023
  11 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 240
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 240 3 3 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 240 (Polychromatic418967fa.accept_19_8_6_12_1_13105 8 177 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 177 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 240 3 2 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 240
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 5 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 177 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 240 3 1 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 240 (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 177 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 240
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 177 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 176 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 176 240 16 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 176 240 (Polychromatic418967fa.accept_17_12_6_2_1_2346 63 176 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 176 240 2 31 88 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 176 240 (accept_3_4 61 176 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 176 240 4 15 44 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 176 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 176 240 2 29 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 176 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 240 8 7 22 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 240 (accept_3_4 55 176 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 240 2 27 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 53
  176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 240 4 13 44 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 240
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 240 2 25 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 240 (accept_3_4 49 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 240 16 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 240 2 23 88 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 240 4 11 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 240 (accept_3_4 43 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 240 2 21 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 240 8 5 22 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 240 2 19 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 240 (accept_3_4 37 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 240 4 9 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 176 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 240 2 17 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 240 (Polychromatic418967fa.accept_21_12_8_9_1_8447
  33 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 240 16 2 11 15
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 240
  (accept_3_4 31 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 240 2 15 88 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 240 4 7 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 176 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 240 2 13 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 240 (accept_3_4 25 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 240 8 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 240 (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 176
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 240 2 11 88 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 240 4 5 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 240 (accept_3_4 19 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  176 240 2 9 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 240 16 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675
  15 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 240 2 7 88 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 240
  (accept_3_4 13 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 240 4 3 44 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 240 2 5 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 176 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 240 8 1 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 240 (accept_3_4 7 176 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 240 2 3 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 240 (Polychromatic418967fa.accept_23_5_15_10_1_14335 5 176
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 240 4 1 44 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 240 2 1 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 240 (accept_3_4 1 176 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 175 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 175 240 5 13 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 175 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 175 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 175 240 (accept_3_5 62 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 175 240 5 12 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 175 240 (accept_3_5 59 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 175 240 (Polychromatic418967fa.accept_19_1_4_12_1_6275 58 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 175 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 240 (accept_3_5 56 175 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 175 240 5 11 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 175 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 240 (accept_3_5 53 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 51 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 175 240 5 10 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 175 240
  (Polychromatic418967fa.accept_19_11_4_12_1_6106 49 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 240 (accept_3_5 47 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 175 240 5 9 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 175 240 (accept_3_5 44 175 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273
  43 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 240
  (Polychromatic418967fa.accept_23_19_14_10_1_12916 42 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 175 240 (accept_3_5 41 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 175 240 5 8 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 175 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 240 (accept_3_5 38 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 175 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 240
  (Polychromatic418967fa.accept_21_15_7_9_1_11550 36 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 175 240 5 7 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 240
  (Polychromatic418967fa.accept_14_5_7_2_1_468 33 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 240 (accept_3_5 32 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 240 (Polychromatic418967fa.accept_17_14_5_2_1_4559 31 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 175 240 5 6 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 175 240 (accept_3_5 29 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 175 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 240 (Polychromatic418967fa.accept_18_9_13_6_1_877 27 175
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 240 (accept_3_5 26 175
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 175 240 5 5 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 175 240
  (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 240 (accept_3_5 23 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 240 (Polychromatic418967fa.accept_27_22_13_24_1_14456 22 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 175 240 5 4 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 240 (Polychromatic418967fa.accept_21_18_7_9_1_2529 18 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 240 (accept_3_5 17 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 240 5 3 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 175 240 (accept_3_5 14 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 240 (Polychromatic418967fa.accept_21_13_7_9_1_2528 13 175
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 240 (accept_3_5 11 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  175 240 5 2 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 175 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 175 240 (accept_3_5 8 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 175 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 240 (Polychromatic418967fa.accept_19_6_4_12_1_6193 6 175
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 240 5 1 35 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 240
  (Polychromatic418967fa.accept_22_4_21_20_1_14455 4 175 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 240 (accept_3_5 2 175 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 174 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 174 240 6 11 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 174 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 240 2 32 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 174 240 3 21 58 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 240 2 31 87 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 240 6 10 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 174 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 240 2 29 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 174 240 3 19 58 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 240 2 28 87 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 240 6 9 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 174 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 240 2 26 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 240 3 17 58 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 240 2 25 87 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 240 6 8 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 240 2 23 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 240 3 15 58 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 240 2 22 87 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 240 6 7 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 240 2 20 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 240 3 13 58 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 240 2 19 87 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 240 6 6 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 240 2 17 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 240 3 11 58 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 240 2 16 87 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 240 6 5 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 174 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 240 2 14 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 240 3 9 58 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 240 2 13 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 240 6 4 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 240 2 11 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 240 3 7 58 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 240 2 10 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 240 6 3 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 240 2 8 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 240 3 5 58 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 240 2 7 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 240 6 2 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 240 2 5 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 240 3 3 58 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 240 2 4 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 240 6 1 29 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 174 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 240 2 2 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 174 240 3 1 58 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 174 240 2 1 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 174 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 68 173 240 (Eq.refl Bool.true) (allA_succ_of_accept 67 173 240 (accept_3_4 67 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 240
  (Polychromatic418967fa.accept_11_10_8_9_1_492 65 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 240 (accept_3_4 64 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 240 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 240 (accept_3_4 61 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 240 (accept_3_4 58 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 240 (Polychromatic418967fa.accept_17_5_3_2_1_5847 56 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 240 (accept_3_4 55 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 173
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 240 (accept_3_4 52 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 240 (Polychromatic418967fa.accept_18_15_11_6_1_4067 51 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 240 (accept_3_4 49 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 240
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 240 (accept_3_4 46 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 240 (accept_3_4 43 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 240 (Polychromatic418967fa.accept_19_4_2_12_1_10527 42 173 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 240 (accept_3_4 40 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 240 (accept_3_4 37 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 240 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 173 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 240 (accept_3_4 34 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 240 (accept_3_4 31 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 240
  (Polychromatic418967fa.accept_19_10_2_12_1_6242 29 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 173 240 (accept_3_4 28 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 173 240 (Polychromatic418967fa.accept_25_2_23_15_1_14454 27 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 240 (Polychromatic418967fa.accept_9_8_2_6_1_875
  26 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 240 (accept_3_4 25
  173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 173 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 173 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 240 (accept_3_4 22 173 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 173 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221
  20 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 240 (accept_3_4 19
  173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 173 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 240 (accept_3_4 16 173 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 173 240 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 240
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 240 (accept_3_4 13 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 240 (accept_3_4 10 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 240 (accept_3_4 7 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 240 (Polychromatic418967fa.accept_19_6_2_12_1_6136 6 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 240 (accept_3_4 4 173 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 173 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 240
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 240 (accept_3_4 1 173 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 172 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 172 240 4 17 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 172 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 172 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 172 240 2 33 86 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 172 240 (accept_3_5 65 172 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 172 240 4 16 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 172 240
  (Polychromatic418967fa.accept_23_17_11_10_1_11257 63 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 172 240 2 31 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 172 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 172 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 172 240 4 15 43 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 172 240 (accept_3_5 59 172 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 172 240 2 29 86 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 172 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 172 240 4 14 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 172 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 172 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 172 240 2 27 86 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 172 240 (accept_3_5 53 172 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 172 240 4 13 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 172 240 (Polychromatic418967fa.accept_14_9_4_2_1_983
  51 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 240 2 25 86 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 240 4 12 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 240 (accept_3_5 47 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 240 2 23 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 240 (Polychromatic418967fa.accept_19_7_1_12_1_6134 45 172 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 240 4 11 43 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 240 2 21 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 240 (accept_3_5 41 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 240 4 10 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 172 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 240 2 19 86 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 240
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 240 4 9 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 240 (accept_3_5 35 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 240 2 17 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 172 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 240 4 8 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 240 2 15 86 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 240 (accept_3_5 29
  172 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 240 4 7 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 240 2 13 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 172 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 240 4 6 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 240 (accept_3_5 23 172 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 240 2 11 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 240 4 5 43 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 240 2 9 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 240 (accept_3_5 17 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 240 4 4 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 15 172 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 240 2 7 86 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 240 4 3 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 172 240 (accept_3_5 11 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  172 240 2 5 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 172 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 172 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 240 4 2 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 172 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 240 2 3 86 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 240 (accept_3_5 5
  172 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 240 4 1 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 172 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 240 2 1 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 240 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 172 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 171 240 (Eq.refl Bool.true) (allA_succ_of_gcd 69 171 240 3 23 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 171 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 240 (Polychromatic418967fa.accept_17_16_1_2_1_3403 67 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 171 240 3 22 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 171 240 (Polychromatic418967fa.accept_21_2_3_9_1_1317
  65 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 240 3 21 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 171 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  61 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 240 3 20 57 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 240
  (Polychromatic418967fa.accept_21_17_3_9_1_8524 59 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 240 3 19 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043
  56 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 240 3 18 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 171 240 (Polychromatic418967fa.accept_13_1_2_6_1_515 53 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 240
  (Polychromatic418967fa.accept_21_10_3_9_1_11595 52 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 171 240 3 17 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 171 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 171 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 171 240 3 16 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 171 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 240
  (Polychromatic418967fa.accept_27_19_9_24_1_14453 46 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 171 240 3 15 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 171 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 44 171 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 171 240 3 14 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 171 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  40 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 240 3 13 57 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 240 (Polychromatic418967fa.accept_17_3_1_2_1_12027 37 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 240 3 12 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 240 (Polychromatic418967fa.accept_13_9_2_6_1_514
  35 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 171 240 3 11 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 171 240 (Polychromatic418967fa.accept_18_14_9_6_1_1777 32 171 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 240
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 240 3 10 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 240 (Polychromatic418967fa.accept_21_7_3_9_1_5294
  28 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 240 3 9 57 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 240 3 8 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 240 (Polychromatic418967fa.accept_13_10_2_6_1_1044
  23 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 240 3 7 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 171 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 240 3 6 57 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 240
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 240 (Polychromatic418967fa.accept_17_16_1_2_1_3403 16 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 240 3 5 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 171 240 3 4 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 171 240 (Polychromatic418967fa.accept_22_11_17_20_1_14452 11 171 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 240
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 240 3 3 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 240 (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 171 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 240 3 2 57 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 240 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4 171 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 240 3 1 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025 2 171 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 171 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 170 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 170 240 10 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 240 (Polychromatic418967fa.accept_21_6_2_9_1_5292 69 170
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 170 240 2 34 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 170 240 (accept_3_4 67
  170 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 170 240 2 33 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 170 240 5 13 34 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 170 240 2 32 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 63 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 240 2 31 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 240 (accept_3_4 61 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 240 10 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 170 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 240 2 29 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 240 2 28 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 170 240 5 11 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 170 240 2 27 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 240 (Polychromatic418967fa.accept_19_15_18_12_1_6180 53 170
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 240 2 26 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 240 10 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 240 (accept_3_4 49 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 240 2 24 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 170 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 240 2 23 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 170 240 5 9 34 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 170 240 2 22 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 240 (accept_3_4 43 170 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 240 2 21 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 170 240 10 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 170 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 170 240 2 19 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 170 240 (accept_3_4 37 170 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 170 240 2 18 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 170 240 5 7 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 170 240 2 17 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 240
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 240 2 16 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 240 (accept_3_4 31 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 240 10 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 170 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 240 2 14 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 240
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 27 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 240 2 13 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 170 240 5 5 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 170 240 2 12 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 170 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 170 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 240 2 11 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 240 10 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 240 (accept_3_4 19 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 240 2 9 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 240 (Polychromatic418967fa.accept_19_17_18_12_1_4783 17 170 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 240 2 8 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 170 240 5 3 34 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 170 240 2 7 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 240 (accept_3_4 13
  170 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 240 2 6 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 240 10 1 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 170 240 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 170 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 240 2 4 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 240 (accept_3_4 7 170 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 240 2 3 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 170 240 5 1 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 170 240 2 2 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  170 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 240 2 1 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 240 (accept_3_4 1
  170 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 169 240 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 169 240 (accept_3_5 71 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 169 240 (Polychromatic418967fa.accept_22_4_15_20_1_14451 70 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 240 (accept_3_5 68 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 240 (accept_3_5 65 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 240 (Polychromatic418967fa.accept_18_9_7_6_1_5331 63 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 240 (accept_3_5 62 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 240 (Polychromatic418967fa.accept_22_17_15_20_1_14450 61
  169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 240
  (Polychromatic418967fa.accept_19_3_17_12_1_6176 60 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 169 240 (accept_3_5 59 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 169 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 240 (accept_3_5 56 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  55 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 240
  (Polychromatic418967fa.accept_21_12_1_9_1_3873 54 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 240 (accept_3_5 53 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 240 (Polychromatic418967fa.accept_22_7_15_20_1_14374 51 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 240 (accept_3_5 50 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 240 (accept_3_5 47 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 240 (accept_3_5 44 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 240 (Polychromatic418967fa.accept_19_5_17_12_1_6120 43 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 240
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 42 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 169 240 (accept_3_5 41 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 169 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 240 (accept_3_5 38 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 240
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 240 (accept_3_5 35 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 240 (Polychromatic418967fa.accept_19_14_17_12_1_6099 33 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 240 (accept_3_5 32 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 240 (accept_3_5 29 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 240 (accept_3_5 26 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 240 (Polychromatic418967fa.accept_17_8_16_2_1_10847 25 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 240 (accept_3_5 23 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 240 (accept_3_5 20 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 240
  (Polychromatic418967fa.accept_17_1_16_2_1_1404 18 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 240 (accept_3_5 17 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 240 (Polychromatic418967fa.accept_23_16_8_10_1_14449 16 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 240 (Polychromatic418967fa.accept_19_15_17_12_1_7723 15 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 240 (accept_3_5 14 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  13 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 240 (accept_3_5 11 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 240 (Polychromatic418967fa.accept_18_9_7_6_1_5331 9 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 240 (accept_3_5 8 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 240 (Polychromatic418967fa.accept_22_7_15_20_1_14374 7 169 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 240 (accept_3_5 5 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 169 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 240 (accept_3_5 2 169 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 168 240 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 168 240 24 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 168 240 (Polychromatic418967fa.accept_19_14_16_12_1_13098 71 168 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 240 2 35 84 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 168 240 3 23 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 168 240 4 17 42 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 240
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 67 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 240 6 11 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 240 (Polychromatic418967fa.accept_27_11_6_24_1_14448 65 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 240 8 8 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 168 240 3 21 56 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 240 2 31 84 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 240
  (Polychromatic418967fa.accept_11_6_3_9_1_906 61 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 240 12 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 59 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 240 2 29 84 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 168 240 3 19 56 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 240 8 7 21 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 240
  (Polychromatic418967fa.accept_17_4_15_2_1_4551 55 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 240 6 9 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 240 (Polychromatic418967fa.accept_19_15_16_12_1_4779 53 168 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 240 4 13 42 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 168 240 3 17 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 240 2 25 84 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 240
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 240 24 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 168 240 (Polychromatic418967fa.accept_17_13_15_2_1_654 47 168 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 240 2 23 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 240 3 15 56 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 240 4 11 42 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 240
  (Polychromatic418967fa.accept_19_5_16_12_1_6175 43 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 168 240 6 7 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 168 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 240 8 5 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 240 3 13 56 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 240 2 19 84 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 240
  (Polychromatic418967fa.accept_23_14_7_10_1_14447 37 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 240 12 3 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 240 (Polychromatic418967fa.accept_27_8_6_24_1_14446 35 168 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 240 2 17 84 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 240 3 11 56 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 240 8 4 21 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 240
  (Polychromatic418967fa.accept_13_5_12_6_1_508 31 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 240 6 5 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 168 240 (Polychromatic418967fa.accept_22_7_14_20_1_14430 29 168 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 240 4 7 42 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 240 3 9 56 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 240 2 13 84 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 240
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 25 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 168 240 24 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 168 240 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 240 2 11 84 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 240 3 7 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 240 4 5 42 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 240
  (Polychromatic418967fa.accept_25_19_18_15_1_11029 19 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 168 240 6 3 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 168 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 240 8 2 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 240 3 5 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 240 2 7 84 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 240
  (Polychromatic418967fa.accept_17_13_15_2_1_654 13 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 240 12 1 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 240 (Polychromatic418967fa.accept_22_11_14_20_1_14445 11 168 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 240 2 5 84 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 240 3 3 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 240 8 1 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 168 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 240 6 1 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 240 (Polychromatic418967fa.accept_13_5_12_6_1_508 5 168 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 240 4 1 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 240 3 1 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 240 2 1 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 240 (Polychromatic418967fa.accept_22_1_14_20_1_9826 1 168
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 167 240 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 167 240 (accept_3_4 73 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 167 240 (Polychromatic418967fa.accept_22_6_13_20_1_12949 72 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 71
  167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 240 (accept_3_4 70
  167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 240
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 69 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 167 240 (Polychromatic418967fa.accept_28_12_27_16_1_14444 68 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 240 (accept_3_4 67 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 240 (accept_3_4 64 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 240 (Polychromatic418967fa.accept_19_6_15_12_1_6263 63 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 240 (accept_3_4 61 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 240 (accept_3_4 58 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 240 (accept_3_4 55 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 240 (Polychromatic418967fa.accept_17_3_14_2_1_646 54 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 240 (accept_3_4 52 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 240 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 240 (accept_3_4 49 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 240 (accept_3_4 46 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 240 (accept_3_4 43 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 240 (Polychromatic418967fa.accept_23_19_6_10_1_14443 42 167 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 240
  (Polychromatic418967fa.accept_19_3_15_12_1_9110 41 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 240 (accept_3_4 40 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 167 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 167 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 240 (accept_3_4 37 167 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 240 (accept_3_4 34 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 240 (Polychromatic418967fa.accept_17_16_14_2_1_5841 33 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 240 (accept_3_4 31 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 240 (accept_3_4 28 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 240 (Polychromatic418967fa.accept_19_8_15_12_1_2240 27 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 240 (accept_3_4 25 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 240
  (Polychromatic418967fa.accept_21_2_20_9_1_2507 23 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 240 (accept_3_4 22 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 240 (accept_3_4 19 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 240 (accept_3_4 16 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 240 (Polychromatic418967fa.accept_21_14_20_9_1_5306 14 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 240 (accept_3_4 13 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 167 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 240 (accept_3_4 10 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 240 (Polychromatic418967fa.accept_25_9_17_15_1_14424 9 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 240 (accept_3_4 7 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 240 (Polychromatic418967fa.accept_19_6_15_12_1_6263 6 167 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 240
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 240 (accept_3_4 4 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 240 (accept_3_4 1 167 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 75 166 240 (Eq.refl Bool.true) (allA_succ_of_gcd 74 166 240 2 37 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 240 2 36 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 240 (accept_3_5 71 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 240 2 35 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 240 (Polychromatic418967fa.accept_13_4_10_6_1_989 69 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 240 2 34 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 240 2 33 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 240 (accept_3_5 65 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 240 2 32 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 240 2 31 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 61 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 240 2 30 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 240 (accept_3_5 59 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 240 2 29 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 166 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 240 2 28 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 240 2 27 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 240 (accept_3_5 53 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 240 2 26 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 240 (Polychromatic418967fa.accept_13_12_10_6_1_3212 51 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 240 2 25 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 240
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 240 2 24 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 240 (accept_3_5 47 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 240 2 23 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 166 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 240 2 22 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 240 2 21 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 240 (accept_3_5 41 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 240 2 20 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 166 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 240 2 19 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 240 2 18 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 240 (accept_3_5 35 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 240 2 17 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 240 (Polychromatic418967fa.accept_18_15_4_6_1_1763 33 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 240 2 16 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 240 2 15 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 240 (accept_3_5 29 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 240 2 14 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 240 (Polychromatic418967fa.accept_28_27_26_16_1_14442 27 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 240 2 13 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 240 2 12 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 240 (accept_3_5 23 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 240 2 11 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 166 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 240 2 10 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 240 2 9 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 240 (accept_3_5 17 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 240 2 8 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 240 2 7 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 240
  (Polychromatic418967fa.accept_19_13_14_12_1_4797 13 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 166 240 2 6 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 240 (accept_3_5 11 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 240 2 5 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 240 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 166 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 240 2 4 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 240 2 3 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 240 (accept_3_5 5 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  240 2 2 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 166 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 240 2 1 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 166 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 165 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 165 240 15 5 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 165 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 165 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 165 240 3 24 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 165 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 165 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 165 240 5 14 33 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 165 240 3 23 55 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 165 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 165 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 240 3 22 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 165 240 5 13 33 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 165 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 165 240 3 21 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 165 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 165 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 240 (Polychromatic418967fa.accept_7_5_4_2_1_235
  61 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 240 15 4 11 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 240 3 19 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 240 5 11 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 165 240 3 18 55 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 240 3 17 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 165 240 5 10 33 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 240 3 16 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 165 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 240 15 3 11 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 240 3 14 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 240 5 8 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 165 240 3 13 55 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 240 3 12 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 165 240 5 7 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 34
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 240 3 11 55 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 240 15 2 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 240 3 9 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 240 5 5 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 165 240 3 8 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 240 3 7 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 165 240 5 4 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 165 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 240 3 6 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 165 240 15 1 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 165 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 165 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 240 (Polychromatic418967fa.accept_7_6_4_2_1_236
  13 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 240 3 4 55 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 165 240 5 2 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 165 240 3 3 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 240 3 2 55 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 165 240 5 1 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 240
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 240 3 1 55 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 240 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 164 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 164 240 4 19 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 164 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 164 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 164 240 2 37 82 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 164 240 (accept_3_4 73 164 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 164 240 4 18 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 164 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 164 240 2 35 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 164 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 164 240 4 17 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 164 240 (accept_3_4 67 164 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 164 240 2 33 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 164 240 (Polychromatic418967fa.accept_21_2_17_9_1_6895
  65 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 240 4 16 41 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 240 2 31 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 240 (accept_3_4 61 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 240 4 15 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 240 2 29 82 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 240 4 14 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 240 (accept_3_4 55 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 240 2 27 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 240 4 13 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 240
  (Polychromatic418967fa.accept_23_5_3_10_1_14441 51 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 164 240 2 25 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 164 240 (accept_3_4 49 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 240 4 12 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 240 2 23 82 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 240
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 240 4 11 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 240 (accept_3_4 43 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 240 2 21 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 240 4 10 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 240 2 19 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 240 (accept_3_4 37 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 240 4 9 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 164 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 240 2 17 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 240 4 8 41 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 240 (accept_3_4 31
  164 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 240 2 15 82 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 240 4 7 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 164 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 240 2 13 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 240 (accept_3_4 25 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 240 4 6 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 164 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 240 2 11 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 240 4 5 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 240 (accept_3_4 19 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 240 2 9 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 164 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 240 4 4 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 240 2 7 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 240 (accept_3_4 13
  164 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 240 4 3 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 240
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 240 2 5 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 164 240 (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 240 4 2 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 240 (accept_3_4 7 164 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 240 2 3 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 240 4 1 41 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 240 2 1 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 240 (accept_3_4 1 164 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 163 240 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 163 240 (accept_3_5 77 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 240 (accept_3_5 74 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 163 240
  (Polychromatic418967fa.accept_21_10_16_9_1_5302 73 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 240 (Polychromatic418967fa.accept_22_6_9_20_1_14440 72 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 240 (accept_3_5 71 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 240
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 240 (accept_3_5 68 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 240 (accept_3_5 65 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 240 (Polychromatic418967fa.accept_13_12_7_6_1_1015 64 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 240
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 63 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 240 (accept_3_5 62 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 240 (accept_3_5 59 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 240 (accept_3_5 56 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 240 (Polychromatic418967fa.accept_21_13_16_9_1_2541 55 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 240 (Polychromatic418967fa.accept_21_12_16_9_1_8497 54 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 240 (accept_3_5 53 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 240
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 240 (accept_3_5 50 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 240 (accept_3_5 47 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 240
  (Polychromatic418967fa.accept_18_9_1_6_1_5301 45 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 240 (accept_3_5 44 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 240 (Polychromatic418967fa.accept_17_8_10_2_1_4546 42 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 240 (accept_3_5 41 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 240
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 240 (accept_3_5 38 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 240 (Polychromatic418967fa.accept_19_18_11_12_1_6163 37 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 240 (Polychromatic418967fa.accept_21_15_16_9_1_5303 36 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 240 (accept_3_5 35 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261
  34 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 240
  (Polychromatic418967fa.accept_21_12_16_9_1_8497 33 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 163 240 (accept_3_5 32 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 240 (accept_3_5 29 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 240
  (Polychromatic418967fa.accept_21_7_16_9_1_2417 28 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 163 240 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 240 (accept_3_5 26 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 240
  (Polychromatic418967fa.accept_19_5_11_12_1_11765 24 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 163 240 (accept_3_5 23 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 240 (accept_3_5 20 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 240
  (Polychromatic418967fa.accept_25_19_13_15_1_5391 19 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 240 (accept_3_5 17 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 240
  (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 163 240 (accept_3_5 14 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 163 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 240 (accept_3_5 11 163 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 240
  (Polychromatic418967fa.accept_19_10_11_12_1_6114 10 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 240 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 240 (accept_3_5 8 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 240
  (Polychromatic418967fa.accept_21_6_16_9_1_5300 6 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 240 (accept_3_5 5 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 163 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 240 (accept_3_5 2 163 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 240 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 163 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 162 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 162 240 6 13 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 162 240 (Polychromatic418967fa.accept_21_14_15_9_1_1339 77 162 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 240 2 38 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 162 240 3 25 54 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 162 240 2 37 81
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 240 6 12 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 162 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 240 2 35 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 162 240 3 23 54 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 240 2 34 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 240
  (Polychromatic418967fa.accept_21_4_15_9_1_3839 67 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 240 6 11 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 162 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 240 2 32 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 240 3 21 54 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 240 2 31 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 240
  (Polychromatic418967fa.accept_21_19_15_9_1_11533 61 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 162 240 6 10 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 162 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 162 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 240 2 29 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 240 3 19 54 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 240 2 28 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 240 6 9 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 240 (Polychromatic418967fa.accept_21_11_15_9_1_3868 53 162 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 240 2 26 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 240 3 17 54 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 240 2 25 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 240
  (Polychromatic418967fa.accept_19_11_10_12_1_2256 49 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 162 240 6 8 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 162 240 (Polychromatic418967fa.accept_19_9_10_12_1_6161 47 162 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 240 2 23 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 240 3 15 54 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 240 2 22 81
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 240
  (Polychromatic418967fa.accept_11_10_8_9_1_492 43 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 240 6 7 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 162 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 240 2 20 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 240 3 13 54 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 240 2 19 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 240
  (Polychromatic418967fa.accept_21_16_15_9_1_6893 37 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 162 240 6 6 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 162 240 (Polychromatic418967fa.accept_21_14_15_9_1_1339 35 162 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 240 2 17 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 240 3 11 54 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 240 2 16 81
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 240 6 5 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 162 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 240 2 14 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 240 3 9 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 240 2 13 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 240
  (Polychromatic418967fa.accept_19_6_10_12_1_11771 25 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 162 240 6 4 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 240 (Polychromatic418967fa.accept_21_2_15_9_1_3838 23 162 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 240 2 11 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 240 3 7 54 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 240 2 10 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 240
  (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 240 6 3 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 240 2 8 81 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 240 3 5 54 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 240 2 7 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 240 6 2 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 240 (Polychromatic418967fa.accept_17_11_9_2_1_8423 11 162 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 240 2 5 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 240 3 3 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 240 2 4 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 240 (Polychromatic418967fa.accept_17_7_9_2_1_629 7
  162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 240 6 1 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 240
  (Polychromatic418967fa.accept_21_5_15_9_1_11534 5 162 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 162 240 2 2 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 162 240 3 1 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 162 240 2 1 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 162 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 162 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 161 240 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 161 240 (accept_3_4 79 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 161 240 (Polychromatic418967fa.accept_17_10_8_2_1_8411 78 161 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 161 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 161 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 240 (accept_3_4 76 161 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 75
  161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 240 (accept_3_4 73 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 240 (Polychromatic418967fa.accept_25_22_11_15_1_14439 72 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 71 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 240 (accept_3_4 70 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 69 161
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 240 (accept_3_4 67 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 240 (accept_3_4 64 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 240 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 62 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 240 (accept_3_4 61 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 240 (accept_3_4 58 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 240 (accept_3_4 55 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 240 (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 240 (Polychromatic418967fa.accept_13_1_5_6_1_1048 53 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 240 (accept_3_4 52 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 240 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 161
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 240 (accept_3_4 49 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 240 (accept_3_4 46 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 240 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 161 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 240
  (Polychromatic418967fa.accept_17_10_8_2_1_8411 44 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 240 (accept_3_4 43 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 240 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 240 (accept_3_4 40 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 240 (accept_3_4 37 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 240 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 240 (accept_3_4 34 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 240 (Polychromatic418967fa.accept_14_5_7_2_1_468 33 161
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 240 (accept_3_4 31 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 240 (accept_3_4 28 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 240
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 240 (accept_3_4 25 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 240 (accept_3_4 22 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 240 (accept_3_4 19 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 240 (Polychromatic418967fa.accept_19_18_9_12_1_6153 18 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 240 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 240 (accept_3_4 16 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 240 (Polychromatic418967fa.accept_18_15_17_6_1_4043 15 161
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 240
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 240 (accept_3_4 13 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 240 (accept_3_4 10 161 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 240 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 161 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 240
  (Polychromatic418967fa.accept_27_8_26_24_1_14438 8 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 161 240 (accept_3_4 7 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 161 240 (Polychromatic418967fa.accept_21_6_14_9_1_6854 6 161 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 240 (accept_3_4 4 161 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 240 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 240 (accept_3_4 1 161 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 160 240 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 160 240 80 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 160 240 (Polychromatic418967fa.accept_21_16_13_9_1_2539 79 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 160 240 2 39 80 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 160 240 (accept_3_5 77 160 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 160 240 4 19 40 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 160 240 5 15 32 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 160 240 2 37 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 160 240 8 9 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 160 240 (accept_3_5 71 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  160 240 10 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 160 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 160 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 240 4 17 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 67
  160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 240 2 33 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 160 240 5 13 32 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 160 240 16 4 10
  15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 240
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 160 240 2 31 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 160 240 (Polychromatic418967fa.accept_13_9_4_6_1_1005 61 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 240 20 3 8 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 240 (accept_3_5 59 160 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 240 2 29 80 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 240 8 7 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 160 240 5 11 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 160 240 2 27 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 160 240 (accept_3_5 53 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 240 4 13 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 240 (Polychromatic418967fa.accept_18_15_16_6_1_1751 51 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 240 10 5 16 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 240 16 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 240 (accept_3_5 47 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 240 2 23 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 160 240 5 9 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 160 240 4 11 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 160 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 240 2 21 80 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 240 (accept_3_5 41 160 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 240 40 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 240 2 19 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 240 4 9 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 160 240 5 7 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 160 240 2 17 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 240 16 2 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 240 10 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 240 (accept_3_5 29 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 240 4 7 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 160 240 (Polychromatic418967fa.accept_21_6_13_9_1_12985 27 160 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 240 2 13 80 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 160 240 5 5 32 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 240 8 3 20 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 240 (accept_3_5 23 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 240 2 11 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 240 20 1 8 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 240
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 240 2 9 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 240 (accept_3_5 17 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 240 16 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 160 240 5 3 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 160 240 2 7 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 160 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 160 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 240 4 3 40 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 240 (accept_3_5 11 160 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 240 10 1 16 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 240
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 240 8 1 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 240 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 160 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 240 2 3 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 160 240 5 1 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 160 240 4 1 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 240 2 1 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 160 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 159
  240 (Eq.refl Bool.true) (allA_succ_of_gcd 81 159 240 3 27 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 159 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 159 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 79 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 159 240 3 26 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 159 240 (Polychromatic418967fa.accept_14_7_5_2_1_2473 77 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 76 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 240 3 25 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 73
  159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 159 240 3 24 53 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 159 240
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 71 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 159 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 240 3 23 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 240
  (Polychromatic418967fa.accept_19_11_7_12_1_4770 68 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 240 3 22 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 240
  (Polychromatic418967fa.accept_18_11_15_6_1_2832 65 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 159 240 (Polychromatic418967fa.accept_17_13_6_2_1_5850 64 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 240 3 21 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 61 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 240 3 20 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 240
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 240 3 19 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 240 (Polychromatic418967fa.accept_19_18_7_12_1_6148 56 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 240
  (Polychromatic418967fa.accept_17_4_6_2_1_5871 55 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 240 3 18 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 52
  159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 240 3 17 53 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 240
  (Polychromatic418967fa.accept_21_8_12_9_1_9980 50 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 240 3 16 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 240 (Polychromatic418967fa.accept_17_13_6_2_1_5850
  47 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 240 3 15 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 240 (Polychromatic418967fa.accept_13_5_3_6_1_3278 44 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 240
  (Polychromatic418967fa.accept_19_5_7_12_1_2252 43 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 240 3 14 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 240 (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 240
  (Polychromatic418967fa.accept_11_7_5_9_1_884 40 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 240 3 13 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 240
  (Polychromatic418967fa.accept_19_18_7_12_1_6148 37 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 159 240 3 12 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 159 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 240
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 34 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 159 240 3 11 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 159 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 240 3 10 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 240
  (Polychromatic418967fa.accept_18_10_15_6_1_6621 28 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 159 240 3 9 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 159 240 (Polychromatic418967fa.accept_21_5_12_9_1_11589 26 159 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 240 3 8 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 240 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 240 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 159
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 240 3 7 53 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 240
  (Polychromatic418967fa.accept_19_1_7_12_1_3443 20 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 240 (Polychromatic418967fa.accept_21_19_12_9_1_9957 19 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 240 3 6 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 240 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 159 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 240 3 5 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 14 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 240 (Polychromatic418967fa.accept_17_13_6_2_1_5850 13 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 240 3 4 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 159 240 3 3 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 240 (Polychromatic418967fa.accept_19_8_7_12_1_14355 8 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 159 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 240 3 2 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 240
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 240 3 1 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 240 (Polychromatic418967fa.accept_21_2_12_9_1_5324 2 159 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 1 159 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 158
  240 (Eq.refl Bool.true) (allA_succ_of_gcd 82 158 240 2 41 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 240 (Polychromatic418967fa.accept_18_9_14_6_1_1790 81 158
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 158 240 2 40 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 158 240 (accept_3_4 79
  158 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 158 240 2 39 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 158 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 77 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 158 240 2 38 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 158 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 158 240 2 37 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 158 240 (accept_3_4 73 158 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 158 240 2 36 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 158 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 71
  158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 240 2 35 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 240 2 34 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 240 (accept_3_4 67 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 240 2 33 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 240 2 32 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 63 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 240 2 31 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 240 (accept_3_4 61 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 240 2 30 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 240 (Polychromatic418967fa.accept_19_2_6_12_1_6270 59 158 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 240 2 29 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 240 2 28 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 240 (accept_3_4 55 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 240 2 27 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 240 2 26 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 240
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 240 2 25 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 240 (accept_3_4 49 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 240 2 24 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 240 2 23 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 240
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 45 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 240 2 22 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 240 (accept_3_4 43 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 240 2 21 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 240 2 20 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 240 2 19 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 240 (accept_3_4 37 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 240 2 18 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 240 2 17 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 240 2 16 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 240 (accept_3_4 31 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 240 2 15 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 240 2 14 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 240 2 13 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 240 (accept_3_4 25 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 240 2 12 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 240 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 158 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 240 2 11 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 240
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 240 2 10 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 240 (accept_3_4 19 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 240 2 9 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 240 2 8 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 240
  (Polychromatic418967fa.accept_19_15_6_12_1_7746 15 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 158 240 2 7 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 158 240 (accept_3_4 13 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 240 2 6 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 158 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 240 2 5 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 240
  (Polychromatic418967fa.accept_13_9_2_6_1_514 9 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 240 2 4 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 240 (accept_3_4 7 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  240 2 3 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 240 2 2 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 158 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 240 2 1 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 240 (accept_3_4 1 158 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 157 240 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 157 240 (accept_3_5 83 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 157 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 157
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 240 (accept_3_5 80 157
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 79 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 240 (accept_3_5 77 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249
  75 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 240 (accept_3_5 74
  157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 157 240 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 240 (accept_3_5 71 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 157 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461
  69 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 240 (accept_3_5 68
  157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 240
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 157 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 240 (accept_3_5 65 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 240
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 63 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 240 (accept_3_5 62 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 240 (Polychromatic418967fa.accept_13_8_1_6_1_997 60 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 240 (accept_3_5 59 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 240 (Polychromatic418967fa.accept_19_1_5_12_1_6249 58 157
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 240 (accept_3_5 56 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 240 (accept_3_5 53 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 240
  (Polychromatic418967fa.accept_19_13_5_12_1_6107 51 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 157 240 (accept_3_5 50 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 157 240 (Polychromatic418967fa.accept_17_15_4_2_1_8419 49 157 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 157 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 240 (accept_3_5 47 157 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 46
  157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 240
  (Polychromatic418967fa.accept_18_9_13_6_1_877 45 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 240 (accept_3_5 44 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 240 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 240 (accept_3_5 41 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 157 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 240 (accept_3_5 38 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 240 (accept_3_5 35 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 240 (accept_3_5 32 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 240 (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 240 (accept_3_5 29 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 240 (accept_3_5 26 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 240 (Polychromatic418967fa.accept_21_3_10_9_1_14437 24 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 240 (accept_3_5 23 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 240 (accept_3_5 20 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 240 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 240 (accept_3_5 17 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 157 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 240 (accept_3_5 14 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 240 (accept_3_5 11 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 240
  (Polychromatic418967fa.accept_13_9_1_6_1_510 9 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 240 (accept_3_5 8 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 240 (accept_3_5 5 157 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 240 (Polychromatic418967fa.accept_19_4_5_12_1_3441 4 157 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 240
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 240 (accept_3_5 2 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 156 240 (Eq.refl Bool.true) (allA_succ_of_gcd 84 156 240 12 7 13 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 156 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 83 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 240 2 41 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 156 240 3 27 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 156 240 4 20 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 156 240 6 13 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 156 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 77 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 240 4 19 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 156 240 3 25 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 240 2 37 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 240 12 6 13 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 240 2 35 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 156 240 3 23 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 240 4 17 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 240 6 11 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 65 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 240 4 16 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 156 240 3 21 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 240 2 31 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 240 12 5 13 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 240 2 29 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 156 240 3 19 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 240 4 14 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 240 6 9 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 240 4 13 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 156 240 3 17 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 240 2 25 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 240 12 4 13 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 240 2 23 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 156 240 3 15 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 240 4 11 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 156 240 6 7 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 156 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 240 4 10 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 156 240 3 13 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 240 2 19 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 156 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 240 12 3 13 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 240 2 17 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 156 240 3 11 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 240 4 8 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 156 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 156 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 240 6 5 26 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 240 4 7 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 156 240 3 9 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 156 240 2 13 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 156 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 240 12 2 13 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 240
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 240 2 11 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 156 240 3 7 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 156 240 4 5 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 156 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 240 6 3 26 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 240
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 240 4 4 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 156 240 3 5 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 156 240 2 7 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 156 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 240 12 1 13 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 240 2 5 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 156 240 3 3 52 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 156 240 4 2 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 156 240 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 240 6 1 26 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 5
  156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 240 4 1 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 240 3 1 52 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 240 2 1 78 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 240
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  155 240 (Eq.refl Bool.true) (allA_succ_of_gcd 85 155 240 5 17 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 155 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 240 (accept_3_4 82 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 240 (Polychromatic418967fa.accept_21_18_8_9_1_2457 81 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 155 240 5 16 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 155 240 (accept_3_4 79 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 155 240 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 240 (accept_3_4 76 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 155 240 5 15 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 155 240
  (Polychromatic418967fa.accept_19_17_3_12_1_13140 74 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 155 240 (accept_3_4 73 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 155 240 (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 155 240 5 14 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 155 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 155 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 68 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 240 (accept_3_4 67 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 155 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 155 240 5 13 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 155 240 (accept_3_4 64 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 240 (Polychromatic418967fa.accept_22_19_1_20_1_4872 63 155
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 240 (accept_3_4 61 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  155 240 5 12 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 240 (accept_3_4 58 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 155 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 155 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 240
  (Polychromatic418967fa.accept_22_12_1_20_1_14436 56 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 155 240 5 11 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 155 240 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 240 (accept_3_4 52 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 240 (Polychromatic418967fa.accept_18_15_11_6_1_4067 51 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 155 240 5 10 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 155 240 (accept_3_4 49 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 240 (Polychromatic418967fa.accept_19_9_3_12_1_6191 47 155
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 240 (accept_3_4 46 155
  240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 155 240 5 9 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 155 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 240 (accept_3_4 43 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 240 (Polychromatic418967fa.accept_26_16_25_6_1_14435 42 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 240 5 8 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 240 (accept_3_4 37 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 240 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 240 5 7 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 240 (accept_3_4 34 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 240
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 155 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 240 (accept_3_4 31 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 155 240 5 6 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 155 240 (Polychromatic418967fa.accept_19_10_3_12_1_10566 29 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 240 (accept_3_4 28 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 240 (Polychromatic418967fa.accept_7_6_1_2_1_230
  27 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 155 240 5 5 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 240 (accept_3_4 22 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 240 (Polychromatic418967fa.accept_9_3_2_6_1_264
  21 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 240 5 4 31 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 240
  (accept_3_4 19 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 240
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 240 (accept_3_4 16 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 155 240 5 3 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 155 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 240 (accept_3_4 13 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 240
  (Polychromatic418967fa.accept_19_11_3_12_1_6138 11 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 155 240 5 2 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 155 240 (Polychromatic418967fa.accept_19_9_3_12_1_6191 9 155 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 240 (accept_3_4 7 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 155 240 5 1 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 155 240 (accept_3_4 4 155 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 155 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 240 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 155
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 240 (accept_3_4 1 155 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 154 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 154 240 2 43 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 240 (Polychromatic418967fa.accept_9_4_1_6_1_284 85 154 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 154 240 2 42 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 154 240 (accept_3_5 83
  154 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 154 240 2 41 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 154 240
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 81 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 154 240 2 40 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 154 240 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 154 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 154 240 2 39 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 154 240 (accept_3_5 77 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 154 240 2 38 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 154 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 75
  154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 240 2 37 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 240
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 73 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 240 2 36 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 240 (accept_3_5 71 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 240 2 35 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 240 (Polychromatic418967fa.accept_13_4_11_6_1_1033 69 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 240 2 34 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 240 2 33 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 240 (accept_3_5 65 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 240 2 32 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 240 (Polychromatic418967fa.accept_19_6_2_12_1_6136 63 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 240 2 31 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 240 2 30 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 240 (accept_3_5 59 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 240 2 29 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 154 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 240 2 28 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 240
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 55 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 154 240 2 27 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 154 240 (accept_3_5 53 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 240 2 26 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 51 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 240 2 25 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 240 2 24 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 240 (accept_3_5 47 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 240 2 23 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 240 (Polychromatic418967fa.accept_21_3_7_9_1_8519 45 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 240 2 22 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 240 2 21 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 240 (accept_3_5 41 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 240 2 20 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 154 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 240 2 19 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 240
  (Polychromatic418967fa.accept_17_3_1_2_1_12027 37 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 240 2 18 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 240 (accept_3_5 35 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 240 2 17 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 240 (Polychromatic418967fa.accept_17_16_1_2_1_3403 33 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 240 2 16 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 240 2 15 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 240 (accept_3_5 29 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 240 2 14 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 240 (Polychromatic418967fa.accept_21_6_7_9_1_5288 27 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 240 2 13 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 240 2 12 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 240 (accept_3_5 23 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 240 2 11 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 154 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 240 2 10 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 240
  (Polychromatic418967fa.accept_21_19_7_9_1_11487 19 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 154 240 2 9 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 240 (accept_3_5 17 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 240 2 8 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 240 (Polychromatic418967fa.accept_18_15_10_6_1_1781 15 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 240 2 7 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 240
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 240 2 6 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 240 (accept_3_5 11 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 240 2 5 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 240 (Polychromatic418967fa.accept_19_9_2_12_1_6243 9 154 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 240 2 4 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 240
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 240 2 3 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 240 (accept_3_5 5 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  240 2 2 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 240 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 240 2 1 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 240 (Polychromatic418967fa.accept_19_1_2_12_1_7725 1 154 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 153 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 153 240 3 29 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 153 240 (Polychromatic418967fa.accept_18_14_9_6_1_1777 86 153
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 85 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 153 240 3 28 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 153 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 83 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 240
  (Polychromatic418967fa.accept_13_4_10_6_1_989 82 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 153 240 3 27 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 153 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 240 (Polychromatic418967fa.accept_18_7_9_6_1_4023
  79 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 153 240 3 26 51 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 153 240
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 77 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 153 240 (Polychromatic418967fa.accept_21_13_6_9_1_1328 76 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 153 240 3 25 51 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 153 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 240 3 24 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 71
  153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 70 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 240 3 23 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 68 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 153 240 3 22 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 153 240 (Polychromatic418967fa.accept_19_8_1_12_1_4804 65 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 64 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 153 240 3 21 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 153 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 62 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 61 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 240 3 20 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 153 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 240
  (Polychromatic418967fa.accept_21_16_6_9_1_8464 58 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 240 3 19 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 56 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 240
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 55 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 240 3 18 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 153 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 153 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 52
  153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 240 3 17 51 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 240 (Polychromatic418967fa.accept_18_13_9_6_1_4024 49 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 240 3 16 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 240 (Polychromatic418967fa.accept_19_9_1_12_1_6234
  47 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 153 240 3 15 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 153 240 (Polychromatic418967fa.accept_13_5_10_6_1_2361 44 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 153 240 3 14 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 153 240 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 153 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 240
  (Polychromatic418967fa.accept_19_2_1_12_1_9092 40 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 240 3 13 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 153 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 240 (Polychromatic418967fa.accept_18_1_9_6_1_6630
  37 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 240 3 12 51 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 240
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 240 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 240 3 11 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 240 3 10 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 153 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 240
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 240 3 9 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 240 (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 153 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 240 3 8 51 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 240
  (Polychromatic418967fa.accept_11_1_10_9_1_871 23 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 240 3 7 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 240 (Polychromatic418967fa.accept_18_2_9_6_1_4025
  20 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 240
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 153 240 3 6 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 153 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 240 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 153
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 240 3 5 51 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 240
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 240 (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 240 3 4 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11
  153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 153 240 3 3 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 240 (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 153 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 240 3 2 51 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 240
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 240 3 1 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 240 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 153 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 152 240 (Eq.refl Bool.true) (allA_succ_of_gcd 88 152 240 8 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 87
  152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 152 240 2 43 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 152 240 (accept_3_4 85
  152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 152 240 4 21 38 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 152 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 83 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 152 240 2 41 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 152 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 152 240 8 10 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 152 240 (accept_3_4 79 152 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 152 240 2 39 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 152 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 77
  152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 240 4 19 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 75 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 240 2 37 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 240 (accept_3_4 73 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 240 8 9 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 152 240 (Polychromatic418967fa.accept_25_21_2_15_1_14412 71 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 240 2 35 76 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 240
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 69 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 240 4 17 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 240 (accept_3_4 67 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 240 2 33 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 240 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 240 8 8 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 240
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 240 2 31 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 240 (accept_3_4 61 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 240 4 15 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 240 2 29 76 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 240 8 7 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 152 240 (accept_3_4 55 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  152 240 2 27 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 152 240 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 152 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 240 4 13 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 240 (Polychromatic418967fa.accept_25_1_2_15_1_3617
  51 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 152 240 2 25 76 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 152 240
  (accept_3_4 49 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 152 240 8 6 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 152 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 152 240 2 23 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 152 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 152 240 4 11 38 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 152 240 (accept_3_4 43 152 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 152 240 2 21 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 240 8 5 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 240 2 19 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 240 (accept_3_4 37 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 240 4 9 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 240 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 152 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 240 2 17 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 240 (Polychromatic418967fa.accept_13_7_9_6_1_148
  33 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 240 8 4 19 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 240
  (accept_3_4 31 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 240 2 15 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 240
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 240 4 7 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 240 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 152 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 240 2 13 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 240 (accept_3_4 25 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 240 8 3 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 152 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 240 2 11 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 240
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 240 4 5 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 240 (accept_3_4 19 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 240 2 9 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 240 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 240 8 2 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 240 (Polychromatic418967fa.accept_13_2_9_6_1_501
  15 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 240 2 7 76 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 240
  (accept_3_4 13 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 240 4 3 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 240
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 240 2 5 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 240 (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 240 8 1 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 240 (accept_3_4 7 152 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 240 2 3 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 240 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 152 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 240 4 1 38 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 240
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 240 2 1 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 240 (accept_3_4 1 152 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  240))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 151 240
  (Eq.refl Bool.true) (allA_succ_of_accept 89 151 240 (accept_3_5 89 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 151 240 (Polychromatic418967fa.accept_23_19_13_10_1_11249 88 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 240 (Polychromatic418967fa.accept_11_10_8_9_1_492
  87 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 240 (accept_3_5 86
  151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 240
  (Polychromatic418967fa.accept_9_4_7_6_1_255 85 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 151 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 151 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 240 (accept_3_5 83 151 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 240
  (Polychromatic418967fa.accept_17_13_15_2_1_654 81 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 240 (accept_3_5 80 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 240 (Polychromatic418967fa.accept_13_1_8_6_1_1016 79 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 240 (Polychromatic418967fa.accept_17_10_15_2_1_653 78 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 240 (accept_3_5 77 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 240 (accept_3_5 74 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 240 (Polychromatic418967fa.accept_17_4_15_2_1_4551 72 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 240 (accept_3_5 71 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 240 (Polychromatic418967fa.accept_19_13_18_12_1_3428 70
  151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 240 (accept_3_5 68 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 240 (accept_3_5 65 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 240
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 240 (accept_3_5 62 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 240 (Polychromatic418967fa.accept_21_18_4_9_1_8484 60 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 240 (accept_3_5 59 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 240 (accept_3_5 56 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 240 (accept_3_5 53 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 240 (Polychromatic418967fa.accept_22_8_19_20_1_8208 52 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 51 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 240 (accept_3_5 50 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 240 (accept_3_5 47 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 240
  (Polychromatic418967fa.accept_18_9_7_6_1_5331 45 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 240 (accept_3_5 44 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 240 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 240 (Polychromatic418967fa.accept_23_19_13_10_1_11249 42 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 240 (accept_3_5 41 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 240 (accept_3_5 38 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 240 (Polychromatic418967fa.accept_19_17_18_12_1_4783 36 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 240 (accept_3_5 35 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 240
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 240 (accept_3_5 32 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 240 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 240 (accept_3_5 29 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 240
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 240 (accept_3_5 26 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 240 (Polychromatic418967fa.accept_19_6_18_12_1_6125 25 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 240 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 240 (accept_3_5 23 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 151 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 240 (accept_3_5 20 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 240 (Polychromatic418967fa.accept_21_18_4_9_1_8484 18 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 240 (accept_3_5 17 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 240 (Polychromatic418967fa.accept_21_16_4_9_1_11526 16 151
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 240
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 240 (accept_3_5 14 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 240 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 240 (accept_3_5 11 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 240
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 240 (accept_3_5 8 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 240 (Polychromatic418967fa.accept_17_7_15_2_1_10843 7 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 240 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 240 (accept_3_5 5 151 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 240 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 151 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 240
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 240 (accept_3_5 2 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 240 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 151 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 150 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 150 240 30 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 150 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 150 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 240 2 44 75 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 150 240 3 29 50 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 150 240 2 43 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 150 240 5 17 30
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 150 240 6 14
  25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 240 2 41 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 150 240 3 27 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 240 10 8 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 240 (Polychromatic418967fa.accept_11_2_7_9_1_890 79 150 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 240 6 13 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 240
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 77 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 240 2 38 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 240 15 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 240 2 37 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 240 (Polychromatic418967fa.accept_17_5_14_2_1_4568 73 150
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 240 6 12 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 240 10 7 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 150 240 3 23 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 240 2 34 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 240 (Polychromatic418967fa.accept_17_16_14_2_1_5841 67 150
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 240 6 11 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 240 5 13 30 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 150 240 2 32 75
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 150 240 3 21
  50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 240 2
  31 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150
  240 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 150 240 30 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 240 (Polychromatic418967fa.accept_19_2_17_12_1_6097 59 150 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 240 2 29 75 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 240 3 19 50 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 240 2 28 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 150 240 5 11 30
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 240 6 9 25
  40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 240
  (Polychromatic418967fa.accept_13_1_7_6_1_142 53 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 240 2 26 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 150 240 3 17 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 240 10 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 240 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 150
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 240 6 8 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 240
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 240 2 23 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 150 240 15 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 240 2 22 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 150 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 240 6 7 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 240
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 240 10 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 150 240 3 13 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 240 2 19 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 240 (Polychromatic418967fa.accept_17_3_14_2_1_646 37 150
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 240 6 6 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 240 5 7 30 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 240 2 17 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 240 3 11 50
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 240 2 16
  75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 240
  (Polychromatic418967fa.accept_21_10_3_9_1_11595 31 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 240 30 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 240 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 240 2 14 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 240 3 9 50 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 240 2 13 75 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 240 5 5 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 240 6 4 25 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 240
  (Polychromatic418967fa.accept_21_2_3_9_1_1317 23 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 240 2 11 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 240 3 7 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 240 10 2 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 240 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 150 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 240 6 3 25 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 240
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 240 2 8 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 150 240 15 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 240 2 7 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 240 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 150 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 240 6 2 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 240
  (Polychromatic418967fa.accept_27_11_15_24_1_14434 11 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 150 240 10 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 240 3 3 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 240 2 4 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 150 240 (Polychromatic418967fa.accept_21_7_3_9_1_5294 7 150 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 240 6 1 25 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 240 5 1 30 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 240 2 2 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 240 3 1 50 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 240 2 1 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 240
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 92 149 240 (Eq.refl Bool.true) (allA_succ_of_accept 91 149 240 (accept_3_4 91 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 240 (Polychromatic418967fa.accept_19_14_16_12_1_13098 90 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 240 (accept_3_4 88 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 87 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 240 (Polychromatic418967fa.accept_17_1_13_2_1_7086 86 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 240 (accept_3_4 85 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 83 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 240 (accept_3_4 82 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 240 (Polychromatic418967fa.accept_14_11_9_2_1_6382 81 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 80 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 240 (accept_3_4 79 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 240 (Polychromatic418967fa.accept_21_15_2_9_1_9962 78 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 240
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 77 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 240 (accept_3_4 76 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 74 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 240 (accept_3_4 73 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 240 (Polychromatic418967fa.accept_19_15_16_12_1_4779 72 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 240 (accept_3_4 70 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 240 (Polychromatic418967fa.accept_23_22_11_10_1_6063 68 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 240 (accept_3_4 67 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 240 (accept_3_4 64 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 240 (Polychromatic418967fa.accept_14_7_9_2_1_2489 63 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 240 (accept_3_4 61 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 240
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 59 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 240 (accept_3_4 58 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 240 (accept_3_4 55 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 240 (Polychromatic418967fa.accept_21_12_2_9_1_6866 54 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 240 (accept_3_4 52 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 51 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 240 (Polychromatic418967fa.accept_26_24_19_6_1_14433 50 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 240 (accept_3_4 49 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 240 (accept_3_4 46 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 240 (Polychromatic418967fa.accept_19_7_16_12_1_10556 45 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 240 (accept_3_4 43 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 240 (Polychromatic418967fa.accept_19_4_16_12_1_485 42 149
  240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 240
  (Polychromatic418967fa.accept_17_7_13_2_1_10840 41 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 149 240 (accept_3_4 40 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 149 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 240 (accept_3_4 37 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  36 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 240 (accept_3_4 34 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 240 (Polychromatic418967fa.accept_18_15_5_6_1_5293 33 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 240 (accept_3_4 31 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 240 (accept_3_4 28 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 240 (Polychromatic418967fa.accept_21_6_2_9_1_5292 27 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 240 (accept_3_4 25 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 240 (Polychromatic418967fa.accept_17_7_13_2_1_10840 24 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 240
  (Polychromatic418967fa.accept_17_6_13_2_1_4549 23 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 240 (accept_3_4 22 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 240 (accept_3_4 19 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 240 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 240
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 240 (accept_3_4 16 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 240 (Polychromatic418967fa.accept_17_15_13_2_1_3418 15 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 240 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 240 (accept_3_4 13 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 149 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 240
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 240 (accept_3_4 10 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 240 (Polychromatic418967fa.accept_19_9_16_12_1_4760 9 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 240 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 240 (accept_3_4 7 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 240 (Polychromatic418967fa.accept_17_6_13_2_1_4549 6 149 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 240
  (Polychromatic418967fa.accept_19_5_16_12_1_6175 5 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 240 (accept_3_4 4 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 240 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 149 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 240 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 240 (accept_3_4 1 149 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 148 240
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 148 240 4 23 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 240 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 148 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 148 240 2 45 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 148 240 (accept_3_5 89
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 148 240 4 22 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 148 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 148 240 2 43 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 148 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 85 148 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 148 240 4 21 37 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 148 240 (accept_3_5 83 148 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 148 240 2 41 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 148 240
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 81 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 148 240 4 20 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 148 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 148 240 2 39 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 148 240 (accept_3_5 77 148 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 148 240 4 19 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 148 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 75
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 240 2 37 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 240
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 240 4 18 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 240 (accept_3_5 71 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 240 2 35 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 240 4 17 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 240
  (Polychromatic418967fa.accept_25_17_23_15_1_14432 67 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 148 240 2 33 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 148 240 (accept_3_5 65 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 240 4 16 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 240 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 148 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 240 2 31 74 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 61 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 240 4 15 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 240 (accept_3_5 59 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 240 2 29 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 240 4 14 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 240 2 27 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 240 (accept_3_5 53 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 240 4 13 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 240 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 240 2 25 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 240
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 240 4 12 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 240 (accept_3_5 47 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 240 2 23 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 240 4 11 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 240
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 240 2 21 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 240 (accept_3_5 41 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 240 4 10 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 240 2 19 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 240 4 9 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 240 (accept_3_5 35 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 240 2 17 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 240 (Polychromatic418967fa.accept_18_15_4_6_1_1763 33 148 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 240 4 8 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 240 2 15 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 240 (accept_3_5 29
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 240 4 7 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 240
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 148 240 2 13 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 148 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 240 4 6 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 240 (accept_3_5 23 148 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 240 2 11 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 240 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 240 4 5 37 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 240 2 9 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 240 (accept_3_5 17 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 240 4 4 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 240 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 148 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 240 2 7 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 240 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 240 4 3 37 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 240 (accept_3_5 11
  148 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 240 2 5 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 240
  (Polychromatic418967fa.accept_25_9_23_15_1_14431 9 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 148 240 4 2 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 148 240 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 148 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 240 2 3 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 240 (accept_3_5 5 148 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 240 4 1 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 240 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 240 2 1 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 240
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 148 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 94 147 240 (Eq.refl Bool.true) (allA_succ_of_gcd 93 147 240 3 31 49 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 92 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 147 240 3 30 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 89
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 88 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 147 240 3 29 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 86 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  85 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 147 240 3 28 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 83 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 240 3 27 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 80
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 147 240 3 26 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  76 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 147 240 3 25 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 74 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 147 240 3 24 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 71
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 70 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 147 240 3 23 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 68 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  67 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 147 240 3 22 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 65 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 147 240 3 21 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 147 240 3 20 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  58 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 240 3 19 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 240 3 18 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 147 240 3 17 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  49 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 147 240 3 16 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 147 240 3 15 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 240 3 14 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  40 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 240 3 13 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 240 3 12 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 240 3 11 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 147 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 240 3 10 49 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 240 3 9 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 147 240 3 8 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 147 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 240 3 7 49 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 240 3 6 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 147 240 3 5 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 147 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 240 3 4 49 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 240 3 3 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 240 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 240
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 147 240 3 2 49 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 240 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 240 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 240 3 1 49 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 240
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 240 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 240 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 146
  240 (Eq.refl Bool.true) (allA_succ_of_gcd 94 146 240 2 47 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 240 (Polychromatic418967fa.accept_9_3_2_6_1_264 93 146 240
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 146 240 2 46 73 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 146 240 (accept_3_4 91
  146 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 146 240 2 45 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 146 240
  (Polychromatic418967fa.accept_9_8_2_6_1_875 89 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 146 240 2 44 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 146 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 146 240 2 43 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 146 240 (accept_3_4 85 146 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 146 240 2 42 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 146 240 (Polychromatic418967fa.accept_11_6_3_9_1_906
  83 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 240 2 41 73 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 240 2 40 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 240 (accept_3_4 79 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 240 2 39 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 240 2 38 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 75 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 240 2 37 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 240 (accept_3_4 73 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 240 2 36 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 240 2 35 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 240
  (Polychromatic418967fa.accept_21_6_20_9_1_6943 69 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 240 2 34 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 240 (accept_3_4 67 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 240 2 33 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 240 (Polychromatic418967fa.accept_21_2_20_9_1_2507 65 146 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 240 2 32 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 240
  (Polychromatic418967fa.accept_17_12_10_2_1_5835 63 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 146 240 2 31 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 146 240 (accept_3_4 61 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 240 2 30 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 240 2 29 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 240 2 28 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 240 (accept_3_4 55 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 240 2 27 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 240 2 26 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 240
  (Polychromatic418967fa.accept_22_7_14_20_1_14430 51 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 146 240 2 25 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 146 240 (accept_3_4 49 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 240 2 24 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 240 (Polychromatic418967fa.accept_25_22_21_15_1_14429 47 146 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 240 2 23 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 240
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 240 2 22 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 240 (accept_3_4 43 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 240 2 21 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 240 2 20 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 240
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 240 2 19 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 240 (accept_3_4 37 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 240 2 18 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 240 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 240 2 17 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 240
  (Polychromatic418967fa.accept_19_14_13_12_1_2259 33 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 146 240 2 16 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 146 240 (accept_3_4 31 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 240 2 15 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 240 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 240 2 14 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 240
  (Polychromatic418967fa.accept_13_1_3_6_1_158 27 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 240 2 13 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 240 (accept_3_4 25 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 240 2 12 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 240 2 11 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 240
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 240 2 10 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 240 (accept_3_4 19 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 240 2 9 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 240 2 8 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 240
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 240 2 7 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 240 (accept_3_4 13 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 240 2 6 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 240 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 240 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 240 2 5 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 240
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 240 2 4 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 240 (accept_3_4 7 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  240 2 3 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 240 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 146 240 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 240 2 2 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 240 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 146 240 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 240 2 1 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 240 (accept_3_4 1 146 240
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  240)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_240_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


