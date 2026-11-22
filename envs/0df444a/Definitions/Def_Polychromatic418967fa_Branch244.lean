-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch244
-- name    : Polychromatic418967fa_Branch244
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:30:09.427596+00:00
-- url     : https://prove2.me/theorems/25af286d-1aba-42de-8241-53bdcdc79b90
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch244_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_244 : allB 244 244 :=
  allB_succ' 2 243 244 (Eq.refl Bool.true) (allA_succ_of_accept 1 243 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  243 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 244)) (allB_succ' 3 242 244
  (Eq.refl Bool.true) (allA_of_3_1 3 242 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 241 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 241 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 241 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 244 (accept_3_3 2 241 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 244 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 241 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 244)))) (allB_succ' 5 240 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 240 244 4 1 60 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 240 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 240 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 244 2 1 120 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  240 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 244))))) (allB_succ' 6 239 244
  (Eq.refl Bool.true) (allA_of_3_1 6 239 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 238 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 238 244 2 3 119 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 238 244 (accept_3_3 5 238 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 244 2 2 119 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 238 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 244 2 1 119 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 238 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 244))))))) (allB_succ' 8 237 244 (Eq.refl Bool.true) (allA_succ_of_accept 7 237 244
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 237 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 237 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 237 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 244 (accept_3_3 5 237 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 237 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 237 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  237 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 244 (accept_3_3 2 237
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 237 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 244)))))))) (allB_succ' 9 236 244
  (Eq.refl Bool.true) (allA_of_3_1 9 236 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 235 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 235 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 235 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 244 (accept_3_3 8 235 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 235 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 235 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 244 (accept_3_3 5 235 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 244 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 235 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 244 (accept_3_3 2 235 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 235 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 244)))))))))) (allB_succ' 11 234 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 234 244 2 5 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 234 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 234 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 244 2 4 117 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 244
  (Polychromatic418967fa.accept_17_7_13_6_1_811 7 234 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 244 2 3 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 244 (accept_3_3 5 234 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 244 2 2 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 234 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 244 2 1 117 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 244
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 234 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 244))))))))))) (allB_succ' 12 233 244 (Eq.refl Bool.true) (allA_of_3_1 12 233 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 232 244 (Eq.refl Bool.true) (allA_succ_of_gcd 12 232 244 4 3 58 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 232 244 (accept_3_3 11
  232 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 232 244 2 5 116 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 232 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 232 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 232 244 4 2 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 232 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 232 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 244 2 3 116 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 244 (accept_3_3 5 232 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 244 4 1 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 232 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 232 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 244 2 1 116 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 244
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 232 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 244))))))))))))) (allB_succ' 14 231 244 (Eq.refl Bool.true) (allA_succ_of_accept 13 231 244
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 231 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 231 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 244 (accept_3_3 11 231 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 231 244 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 231 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 244
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 231 244 (accept_3_3 8 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  231 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 231 244 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 231 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 244 (accept_3_3 5 231 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 231 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 244
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 244 (accept_3_3 2 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 231 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 244)))))))))))))) (allB_succ' 15 230 244 (Eq.refl Bool.true) (allA_of_3_1 15 230 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 229 244 (Eq.refl Bool.true) (allA_succ_of_accept 15 229 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 244 (accept_3_3 14 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 229 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 244 (accept_3_3 11 229 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 229 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 244 (accept_3_3 8 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 229 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 244 (accept_3_3 5 229 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 229 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 244 (accept_3_3 2 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 229 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 244)))))))))))))))) (allB_succ' 17 228 244 (Eq.refl Bool.true) (allA_succ_of_gcd 16 228 244
  4 4 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228
  244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 228 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 228 244 2 7 114 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 228 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 228 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 244 4 3 57 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 244 (accept_3_3 11 228 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 244 2 5 114 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 228 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 244 4 2 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 228 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 228 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 244 2 3 114 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 244 (accept_3_3 5 228 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 244 4 1 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 228 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 228 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 244 2 1 114 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 244
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 228 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 244))))))))))))))))) (allB_succ' 18 227 244 (Eq.refl Bool.true) (allA_of_3_1 18 227 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 226 244 (Eq.refl Bool.true) (allA_succ_of_gcd 18 226 244 2 9 113 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 226 244
  (accept_3_3 17 226 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 226 244 2 8 113 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 226 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 226 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 226 244 2 7 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 226 244 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 226 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 226 244 2 6 113 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 226 244 (accept_3_3 11 226 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 226 244 2 5 113 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 226 244
  (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 226 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 226 244 2 4 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 226 244 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 226 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 226 244 2 3 113 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 226 244 (accept_3_3 5 226 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 226 244 2 2 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 226 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  226 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 244 2 1 113 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 226 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 244))))))))))))))))))) (allB_succ' 20 225 244 (Eq.refl Bool.true) (allA_succ_of_accept 19 225 244
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 225 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 225 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 244 (accept_3_3 17 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 225 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 225 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 244
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 225 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 225 244 (accept_3_3 14 225 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 225 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 244 (accept_3_3 11 225 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 244
  (Polychromatic418967fa.accept_17_10_4_6_1_3757 10 225 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 225 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 244 (accept_3_3 8 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 225 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 225 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 6
  225 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 244 (accept_3_3 5 225
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 244
  (Polychromatic418967fa.accept_22_4_5_2_1_14739 4 225 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 225 244 (Polychromatic418967fa.accept_16_3_1_4_1_5426 3 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 244 (accept_3_3 2 225 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 225 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 244)))))))))))))))))))) (allB_succ' 21 224 244 (Eq.refl
  Bool.true) (allA_of_3_1 21 224 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 223 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 223 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 244 (accept_3_3 20 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 223 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 223 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 244 (Polychromatic418967fa.accept_13_5_2_10_1_248
  18 223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 244 (accept_3_3 17
  223 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 244
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 223 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 244 (accept_3_3 14 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 223 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 223 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 244 (Polychromatic418967fa.accept_9_3_7_1_1_143
  12 223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 244 (accept_3_3 11
  223 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 244
  (Polychromatic418967fa.accept_12_10_7_4_1_820 10 223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 223 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 244 (accept_3_3 8 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 223 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 223 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 6
  223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 244 (accept_3_3 5 223
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 223 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 223 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 244 (accept_3_3 2 223 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 223 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 223 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 244)))))))))))))))))))))) (allB_succ' 23 222 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 222 244 2 11 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 222 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 222 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 244 2 10 111 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 244
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 19 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 244 2 9 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 244 (accept_3_3 17 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 244 2 8 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 222 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 244 2 7 111 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 244 2 6 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 244 (accept_3_3 11 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 244 2 5 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 222 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 244 2 4 111 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 244 2 3 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 244 (accept_3_3 5 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 244 2 2 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 222 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 244 2 1 111 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 222 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 244))))))))))))))))))))))) (allB_succ' 24 221 244 (Eq.refl Bool.true) (allA_of_3_1 24 221 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 220 244 (Eq.refl Bool.true) (allA_succ_of_gcd 24 220 244 4 6 55 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 244
  (accept_3_3 23 220 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 244 2 11 110 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 220 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 220 244 4 5 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 220 244 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 220 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 220 244 2 9 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 220 244 (accept_3_3 17 220 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 220 244 4 4 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 220 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 220 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 244 2 7 110 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 244
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 220 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 220 244 4 3 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 220 244 (accept_3_3 11 220 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 244 2 5 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 220 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 244 4 2 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7
  220 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 244 2 3 110 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 244 (accept_3_3 5
  220 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 244 4 1 55 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 220 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 244 2 1 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 244 (Polychromatic418967fa.accept_16_1_12_4_1_695 1 220 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 244))))))))))))))))))))))))) (allB_succ' 26 219 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 219 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 219 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 24
  219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 244 (accept_3_3 23
  219 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 219 244 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 244 (accept_3_3 20 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 219 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 244 (Polychromatic418967fa.accept_7_4_2_6_1_337
  18 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 244 (accept_3_3 17
  219 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 219 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 244 (accept_3_3 14 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 219 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 219 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 244 (Polychromatic418967fa.accept_11_1_10_2_1_58
  12 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 244 (accept_3_3 11
  219 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 219 244 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 244 (accept_3_3 8 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 219 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 219 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 6
  219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 244 (accept_3_3 5 219
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 219 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 219 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 244 (accept_3_3 2 219 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 219 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 219 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 244)))))))))))))))))))))))))) (allB_succ' 27 218 244 (Eq.refl
  Bool.true) (allA_of_3_1 27 218 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 217 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 217 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 217 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 244 (accept_3_3 26 217 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 217 244 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 217 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 244
  (Polychromatic418967fa.accept_16_8_9_4_1_630 24 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 244 (accept_3_3 23 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 244 (accept_3_3 20 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 244 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 217 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 244
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 244 (accept_3_3 17 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 244 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 244 (accept_3_3 14 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 217 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 244
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 244 (accept_3_3 11 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 244 (accept_3_3 8 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 244 (Polychromatic418967fa.accept_17_7_13_6_1_811 7 217 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 244
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 244 (accept_3_3 5 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 244 (Polychromatic418967fa.accept_21_4_7_13_1_8757 4 217 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 244 (accept_3_3 2 217 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 217 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 244)))))))))))))))))))))))))))) (allB_succ' 29 216
  244 (Eq.refl Bool.true) (allA_succ_of_gcd 28 216 244 4 7 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 244 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 216
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 244 2 13 108 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 244 4 6 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 244 (accept_3_3 23 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  216 244 2 11 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 216 244 (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 216 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 244 4 5 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 244 (Polychromatic418967fa.accept_16_3_8_4_1_3279
  19 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 244 2 9 108 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 244
  (accept_3_3 17 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 244 4 4 54 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 216 244 2 7 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 216 244 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 216 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 244 4 3 54 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 244 (accept_3_3 11 216 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 244 2 5 108 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 244
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 244 4 2 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 216 244 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 216 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 244 2 3 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 244 (accept_3_3 5 216 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 244 4 1 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 216 244 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 216 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 244 2 1 108 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 244
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 216 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 244))))))))))))))))))))))))))))) (allB_succ' 30 215 244 (Eq.refl Bool.true) (allA_of_3_1 30 215 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 214 244 (Eq.refl Bool.true) (allA_succ_of_gcd 30 214 244 2 15
  107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 214
  244 (accept_3_3 29 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 214 244 2 14 107 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 214 244
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 214 244 2 13 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 214 244 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 214 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 214 244 2 12 107 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 214 244 (accept_3_3 23 214 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 214 244 2 11 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 214 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 214 244 2 10 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 214 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 214 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 214 244 2 9 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 214 244 (accept_3_3 17 214 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 214 244 2 8 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 214 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 15
  214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 244 2 7 107 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 244 2 6 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 244 (accept_3_3 11 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 244 2 5 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 214 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 244 2 4 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 244 2 3 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 244 (accept_3_3 5 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 244 2 2 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 214 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 244 2 1 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 214 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 244))))))))))))))))))))))))))))))) (allB_succ' 32 213 244 (Eq.refl Bool.true) (allA_succ_of_accept 31
  213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 213 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 244 (accept_3_3 29 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 244 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 213 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 244
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 244 (accept_3_3 26 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 244 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 213 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 244 (accept_3_3 23 213 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 213 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 244 (accept_3_3 20 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 244 (accept_3_3 17 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 213 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 244
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 244 (accept_3_3 14 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 244 (accept_3_3 11 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 244 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 213 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 244 (accept_3_3 8 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 244 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 244 (accept_3_3 5 213 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 213 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 244 (accept_3_3 2 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 244)))))))))))))))))))))))))))))))) (allB_succ' 33 212 244 (Eq.refl Bool.true) (allA_of_3_1
  33 212 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 211 244 (Eq.refl Bool.true) (allA_succ_of_accept 33
  211 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 211 244 (accept_3_3 32 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 211 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 211 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 211 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 244 (accept_3_3 29 211 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 244 (Polychromatic418967fa.accept_13_2_3_10_1_658
  28 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 244 (accept_3_3 26 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 244 (accept_3_3 23 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 211 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 244 (accept_3_3 20 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 244 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 211 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 244 (accept_3_3 17 211 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 211 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 244 (accept_3_3 14 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 244 (Polychromatic418967fa.accept_17_13_7_6_1_827 13 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 244 (accept_3_3 11 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 211 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 244 (accept_3_3 8 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 244 (accept_3_3 5 211 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 244 (Polychromatic418967fa.accept_18_4_13_10_1_2064 4 211 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 244 (accept_3_3 2 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 244 (Polychromatic418967fa.accept_16_1_3_4_1_665 1 211 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 244)))))))))))))))))))))))))))))))))) (allB_succ' 35 210 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 210 244 2 17 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 210 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 210 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 210 244 2 16 105 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 244 2 15 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 244 (accept_3_3 29 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 244 2 14 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 210 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 210 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 244 2 13 105 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 244 2 12 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 244 (accept_3_3 23 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 244 2 11 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 210 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 210 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 244 2 10 105 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 244
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 244 2 9 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 244 (accept_3_3 17 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 244 2 8 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 210 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 210 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 244 2 7 105 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 244 2 6 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 244 (accept_3_3 11 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 244 2 5 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 244 2 4 105 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 244 2 3 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 244 (accept_3_3 5 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 244 2 2 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 244 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 210 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 244 2 1 105 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 244
  (Polychromatic418967fa.accept_20_1_10_4_1_7518 1 210 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 244))))))))))))))))))))))))))))))))))) (allB_succ' 36 209 244 (Eq.refl Bool.true) (allA_of_3_1 36 209
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 208 244 (Eq.refl Bool.true) (allA_succ_of_gcd 36 208 244 4
  9 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 208
  244 (accept_3_3 35 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 208 244 2 17 104 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 208 244
  (Polychromatic418967fa.accept_19_14_18_16_1_6530 33 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 208 244 4 8 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 208 244 (Polychromatic418967fa.accept_27_4_19_1_1_14738 31 208 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 208 244 2 15 104 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 208 244 (accept_3_3 29
  208 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 208 244 4 7 52 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 208 244
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 208 244 2 13 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 208 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 208 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 208 244 4 6 52 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 244 (accept_3_3 23 208 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 244 2 11 104 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 244
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 208 244 4 5 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 208 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 208 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 208 244 2 9 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 208 244 (accept_3_3 17 208 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 208 244 4 4 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 208 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 208 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 244 2 7 104 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 244
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 208 244 4 3 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 208 244 (accept_3_3 11 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 208 244 2 5 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 208 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 208 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 244 4 2 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 244 (Polychromatic418967fa.accept_21_7_19_13_1_7164
  7 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 244 2 3 104 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 244
  (accept_3_3 5 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 244 4 1 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 244
  (Polychromatic418967fa.accept_19_3_18_16_1_6483 3 208 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 244 2 1 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 208 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 244))))))))))))))))))))))))))))))))))))) (allB_succ' 38 207 244
  (Eq.refl Bool.true) (allA_succ_of_accept 37 207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 244
  (Polychromatic418967fa.accept_21_15_18_13_1_8747 36 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 244 (accept_3_3 35 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 244 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 244 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 244 (accept_3_3 32
  207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 244
  (Polychromatic418967fa.accept_6_1_3_4_1_1 31 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 207 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 207 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 244 (accept_3_3 29 207 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 207 244 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 244
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 207 244 (accept_3_3 26 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 207 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 244 (accept_3_3 23 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 244
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 207 244 (accept_3_3 20 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 207 244 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 244 (accept_3_3 17 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 207 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 244
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 244 (accept_3_3 14 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 244 (accept_3_3 11 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 244 (accept_3_3 8 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 244 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 244 (accept_3_3 5 207 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 244 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 207 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 244 (accept_3_3 2 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 244)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 206 244 (Eq.refl Bool.true)
  (allA_of_3_1 39 206 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 205 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 205 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 244 (accept_3_3 38 205 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 205 244 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 244 (accept_3_3 35 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 244 (accept_3_3 32 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 244 (accept_3_3 29 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 244 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 244 (accept_3_3 26 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 244 (accept_3_3 23 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 244 (accept_3_3 20 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 244 (accept_3_3 17 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 244 (accept_3_3 14 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 244 (accept_3_3 11 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 244 (accept_3_3 8 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 244 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 244 (accept_3_3 5 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 205 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 244 (accept_3_3 2 205 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 244))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 204 244 (Eq.refl Bool.true) (allA_succ_of_gcd 40 204 244 4 10 51 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 204 244 2 19 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 204 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 204 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 244 4 9 51 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 244 (accept_3_3 35 204 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 244 2 17 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 244 4 8 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 244 2 15 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 204 244 (accept_3_3 29 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 244 4 7 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 204 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 204 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 244 2 13 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 25
  204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 244 4 6 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 244 (accept_3_3 23
  204 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 244 2 11 102 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 244 4 5 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 204 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 244 2 9 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 244 (accept_3_3 17 204 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 244 4 4 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 204 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 244 2 7 102 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 244 4 3 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 244 (accept_3_3 11 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  204 244 2 5 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 204 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 204 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 244 4 2 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 244 2 3 102 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 244 (accept_3_3 5
  204 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 244 4 1 51 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 204 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 244 2 1 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 204 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 244))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 203
  244 (Eq.refl Bool.true) (allA_of_3_1 42 203 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 202 244
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 202 244 2 21 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 202 244 (accept_3_3 41 202 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 202 244 2 20 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 202 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 202 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 244 2 19 101 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 244 2 18 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 244 (accept_3_3 35 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 244 2 17 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 244 2 16 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 244
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 244 2 15 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 244 (accept_3_3 29 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 244 2 14 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 244 2 13 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 244 2 12 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 244 (accept_3_3 23 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 244 2 11 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 244 2 10 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 244 2 9 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 244 (accept_3_3 17 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 244 2 8 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 244 2 7 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 244 2 6 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 244 (accept_3_3 11 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 244 2 5 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 244 2 4 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 244 2 3 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 244 (accept_3_3 5 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 244 2 2 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 202 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 244 2 1 101 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 202 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 244))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 201 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 201 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 201 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 244 (accept_3_3 41 201 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 244 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 201 244 (accept_3_3 38 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 244 (accept_3_3 35 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 201 244 (accept_3_3 32 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 244 (accept_3_3 29 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 244 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 201 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 244
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 244 (accept_3_3 26 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 244 (accept_3_3 23 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 244
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 244 (accept_3_3 20 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 244 (accept_3_3 17 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 244 (accept_3_3 14 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 244 (accept_3_3 11 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 244 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 201
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 244
  (Polychromatic418967fa.accept_13_9_6_10_1_666 9 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 244 (accept_3_3 8 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 244 (accept_3_3 5 201 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 201 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 244
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 244 (accept_3_3 2 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 244)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 200 244 (Eq.refl Bool.true)
  (allA_of_3_1 45 200 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 199 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 199 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 244 (accept_3_3 44 199 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 199 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 244
  (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 244 (accept_3_3 41 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 244 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 244 (accept_3_3 38 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 199 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 244
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 244 (accept_3_3 35 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 244 (accept_3_3 32 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 244 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 199 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 244 (accept_3_3 29 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 244 (accept_3_3 26 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 199 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 244
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 199 244 (accept_3_3 23 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 199 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 199 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 244 (accept_3_3 20 199 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 19
  199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 244 (accept_3_3 17 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 244 (accept_3_3 14 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 199 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 244
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 244 (accept_3_3 11 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 244 (accept_3_3 8 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 244 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 199 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 244
  (Polychromatic418967fa.accept_13_6_4_10_1_660 6 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 244 (accept_3_3 5 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 199 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 244 (accept_3_3 2 199 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 244 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 199 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 244))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 198 244 (Eq.refl Bool.true) (allA_succ_of_gcd 46 198 244 2 23 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 244 2 22 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 198 244 2 21 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 198 244 (accept_3_3 41 198 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 244 2 20 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 198 244 2 19 99 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 244
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 198 244 2 18 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 198 244 (accept_3_3 35 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 198 244 2 17 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 198 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 198 244 2 16 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 244 2 15 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 244 (accept_3_3 29 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 244 2 14 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 244 2 13 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 244 2 12 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 244 (accept_3_3 23 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 198 244 2 11 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 198 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 244 2 10 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 244
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 244 2 9 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 244 (accept_3_3 17 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 244 2 8 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 244 2 7 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 244
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 244 2 6 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 244 (accept_3_3 11 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 244 2 5 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 198 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 244 2 4 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 244
  (Polychromatic418967fa.accept_13_7_3_10_1_656 7 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 244 2 3 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 244 (accept_3_3 5 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  244 2 2 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 198 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 244 2 1 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 198 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 244)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 197 244 (Eq.refl Bool.true) (allA_of_3_1 48 197 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 196 244 (Eq.refl Bool.true) (allA_succ_of_gcd 48 196 244 4 12 49 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 196 244 (accept_3_3 47 196 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 196 244 2 23 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 196 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 45
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 196 244 4 11 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 196 244
  (Polychromatic418967fa.accept_13_4_1_10_1_693 43 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 196 244 2 21 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 196 244 (accept_3_3 41 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 196 244 4 10 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 196 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 196 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 196 244 2 19 98 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 196 244
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 196 244 4 9 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 196 244 (accept_3_3 35 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  196 244 2 17 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 196 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 196 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 244 4 8 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 244 2 15 98 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 244 (accept_3_3 29
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 244 4 7 49 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 244
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 196 244 2 13 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 196 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 196 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 244 4 6 49 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 244 (accept_3_3 23 196 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 244 2 11 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 244 4 5 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 244
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 19 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 196 244 2 9 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 196 244 (accept_3_3 17 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 244 4 4 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 196 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 196 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 244 2 7 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 244 4 3 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 244 (accept_3_3 11
  196 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 244 2 5 98 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 244
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 196 244 4 2 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 196 244 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 196 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 244 2 3 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 244 (accept_3_3 5 196 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 244 4 1 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 196 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 196 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 244 2 1 98 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 244
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 1 196 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 244))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 195 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 195 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 244 (accept_3_3 47 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 244 (Polychromatic418967fa.accept_10_6_5_4_1_571
  46 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 244
  (Polychromatic418967fa.accept_18_9_15_10_1_395 45 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 195 244 (accept_3_3 44 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 195 244 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 244 (accept_3_3 41 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 244
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 244 (accept_3_3 38 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 244 (accept_3_3 35 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 244
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 244 (accept_3_3 32 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 244 (accept_3_3 29 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 244 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 244
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 244 (accept_3_3 26 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 244 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 244 (accept_3_3 23 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 244 (accept_3_3 20 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 244 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 244 (accept_3_3 17 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 244
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 244 (accept_3_3 14 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 195 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 244 (accept_3_3 11 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 244 (Polychromatic418967fa.accept_19_10_5_16_1_6522 10 195 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 244
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 244 (accept_3_3 8 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 244 (accept_3_3 5 195 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 195 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 244 (accept_3_3 2 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 195 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 244)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 194 244 (Eq.refl
  Bool.true) (allA_of_3_1 51 194 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 193 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 193 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 244 (accept_3_3 50 193 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 193 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 244 (accept_3_3 47 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 244 (accept_3_3 44 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 244 (accept_3_3 41 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 244 (accept_3_3 38 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 244
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 244 (accept_3_3 35 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 244 (accept_3_3 32 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 244 (accept_3_3 29 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 244 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 244 (accept_3_3 26 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 244 (accept_3_3 23 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 244 (accept_3_3 20 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 244
  (Polychromatic418967fa.accept_19_18_3_16_1_7962 18 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 193 244 (accept_3_3 17 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 193 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 193 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 244 (accept_3_3 14 193 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 244 (Polychromatic418967fa.accept_8_5_1_4_1_628
  13 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 244 (accept_3_3 11 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 244 (accept_3_3 8 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 244 (accept_3_3 5 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 193 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 244 (accept_3_3 2 193 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 244 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 193 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  244)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 192 244 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 192 244 4 13 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 192 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 192 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 192 244 2 25 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 49
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 192 244 4 12 48 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 192 244 (accept_3_3 47
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 244 2 23 96 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 244
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 192 244 4 11 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 192 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 192 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 192 244 2 21 96 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 192 244 (accept_3_3 41 192 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 244 4 10 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 192 244 2 19 96 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 244 4 9 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 192 244 (accept_3_3 35 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  192 244 2 17 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 192 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 192 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 244 4 8 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 31
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 244 2 15 96 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 244 (accept_3_3 29
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 244 4 7 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 244 2 13 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 192 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 244 4 6 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 244 (accept_3_3 23 192 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 244 2 11 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 244 (Polychromatic418967fa.accept_17_4_5_6_1_8717
  21 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 244 4 5 48 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 244
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 244 2 9 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 244 (accept_3_3 17 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 244 4 4 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 192 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 192 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 244 2 7 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 244 4 3 48 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 244 (accept_3_3 11
  192 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 244 2 5 96 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 244 4 2 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 244 2 3 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 244 (accept_3_3 5 192 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 244 4 1 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 244 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 192 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 244 2 1 96 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 244
  (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 192 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 244))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 191 244 (Eq.refl Bool.true)
  (allA_of_3_1 54 191 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 190 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 190 244 2 27 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 190 244 (accept_3_3 53 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 190 244 2 26 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 190 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 190 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 190 244 2 25 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 190 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 190 244 2 24 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 190 244 (accept_3_3 47 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 190 244 2 23 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 190 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 190 244 2 22 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 190 244 2 21 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 190 244 (accept_3_3 41 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 244 2 20 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 244 (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 244 2 19 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 190 244 2 18 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 190 244 (accept_3_3 35 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 190 244 2 17 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 190 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 190 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 244 2 16 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 244 2 15 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 244 (accept_3_3 29 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 244 2 14 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 244 (Polychromatic418967fa.accept_37_27_5_22_1_14737 27 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 244 2 13 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 244 2 12 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 244 (accept_3_3 23 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 244 2 11 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 244 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 244 2 10 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 244 2 9 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 244 (accept_3_3 17 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 244 2 8 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 244 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 244 2 7 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 244 2 6 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 244 (accept_3_3 11 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 244 2 5 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 190 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 244 2 4 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 244 2 3 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 244 (accept_3_3 5 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  244 2 2 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 244 (Polychromatic418967fa.accept_22_3_14_2_1_13240 3 190 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 244 2 1 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 190 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 189 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 244 (accept_3_3 53 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 244 (Polychromatic418967fa.accept_17_1_2_6_1_818
  52 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 244
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 244 (accept_3_3 50 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 189
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 244 (accept_3_3 47 189
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 244
  (Polychromatic418967fa.accept_17_12_2_6_1_2630 46 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 189 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 244 (accept_3_3 44 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 244 (Polychromatic418967fa.accept_12_6_9_4_1_96
  42 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 244 (accept_3_3 41
  189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 244
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 189 244 (Polychromatic418967fa.accept_16_7_13_4_1_1348 39 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 244 (accept_3_3 38 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 244 (Polychromatic418967fa.accept_14_8_7_6_1_1159
  36 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 244 (accept_3_3 35
  189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 244
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 34 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 189 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 244 (accept_3_3 32 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 244 (Polychromatic418967fa.accept_12_6_9_4_1_96
  30 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 244 (accept_3_3 29
  189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 244
  (Polychromatic418967fa.accept_10_8_9_4_1_961 28 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 189 244 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 244 (accept_3_3 26 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 244
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 244 (accept_3_3 23 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 244 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 244 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 189 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 244 (accept_3_3 20 189 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 244
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 244 (accept_3_3 17 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 244 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 189 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 189 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 244 (accept_3_3 14 189 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 244
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 244 (accept_3_3 11 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 244 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 189 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 244 (accept_3_3 8 189 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 244 (accept_3_3 5 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 244 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 189 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 244 (accept_3_3 2 189 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 188 244 (Eq.refl Bool.true) (allA_of_3_1 57
  188 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 187 244 (Eq.refl Bool.true) (allA_succ_of_accept 57
  187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 187 244 (accept_3_3 56 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 187 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 244 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 187
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 187 244 (accept_3_3 53 187
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 187 244
  (Polychromatic418967fa.accept_10_2_7_4_1_967 52 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 244 (accept_3_3 50 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 187 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 244 (Polychromatic418967fa.accept_9_3_7_1_1_143
  48 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 244 (accept_3_3 47
  187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 187 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 244 (accept_3_3 44 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 187 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 244 (Polychromatic418967fa.accept_9_6_7_1_1_145
  42 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 244 (accept_3_3 41
  187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 40 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 244 (accept_3_3 38 187 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 187 244 (Polychromatic418967fa.accept_20_17_7_4_1_7671 37 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 244 (accept_3_3 35 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 244 (accept_3_3 32 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 244 (accept_3_3 29 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 244 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 244 (accept_3_3 26 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 244 (accept_3_3 23 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 244 (accept_3_3 20 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 244 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 187 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 244 (accept_3_3 17 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 244 (Polychromatic418967fa.accept_21_16_19_13_1_7140 16 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 244 (accept_3_3 14 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 187 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 244 (accept_3_3 11 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 244 (accept_3_3 8 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 244 (accept_3_3 5 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 187 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 244 (accept_3_3 2 187 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 187 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 186 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 186 244 2 29 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 186 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 186 244 2 28 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 244 2 27 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 244 (accept_3_3 53 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 186 244 2 26 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 186 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 186 244 2 25 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 244 2 24 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 244 (accept_3_3 47 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 186 244 2 23 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 244 2 22 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 244 2 21 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 244 (accept_3_3 41 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 244 2 20 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 244 2 19 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 244 2 18 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 244 (accept_3_3 35 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 244 2 17 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 244 2 16 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 244 2 15 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 244 (accept_3_3 29 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 244 2 14 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 244 2 13 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 244 2 12 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 244 (accept_3_3 23 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 244 2 11 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 244 2 10 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 244 2 9 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 244 (accept_3_3 17 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 244 2 8 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 244 2 7 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 244 2 6 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 244 (accept_3_3 11 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 244 2 5 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 186 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 244 2 4 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 244 2 3 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 244 (accept_3_3 5 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  244 2 2 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 186 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 244 2 1 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 244 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 186 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 185 244 (Eq.refl Bool.true) (allA_of_3_1
  60 185 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 184 244 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  184 244 4 15 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 184 244 (accept_3_3 59 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  184 244 2 29 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 184 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 184 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 184 244 4 14 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 184 244 (Polychromatic418967fa.accept_13_3_2_10_1_2697
  55 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 244 2 27 92 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 244
  (accept_3_3 53 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 244 4 13 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 184 244 2 25 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 184 244 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 184 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 184 244 4 12 46 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 184 244 (accept_3_3 47 184 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 184 244 2 23 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 184 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 45
  184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 244 4 11 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 184 244 2 21 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 184 244 (accept_3_3 41 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 184 244 4 10 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 184 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 184 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 244 2 19 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 244
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 184 244 4 9 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 184 244 (accept_3_3 35 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 184 244 2 17 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 184 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 184 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 244 4 8 46 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 244 2 15 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 244 (accept_3_3 29 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 244 4 7 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 184 244 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 184 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 244 2 13 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 25
  184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 244 4 6 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 244 (accept_3_3 23
  184 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 244 2 11 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 184 244 4 5 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 184 244 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 184 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 244 2 9 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 244 (accept_3_3 17 184 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 244 4 4 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 184 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 244 2 7 92 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 244
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 244 4 3 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 184 244 (accept_3_3 11 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  184 244 2 5 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 184 244 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 184 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 244 4 2 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 244 2 3 92 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 244 (accept_3_3 5
  184 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 244 4 1 46 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 184 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 184 244 2 1 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 184 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 184 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 184 244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 183 244 (Eq.refl Bool.true) (allA_succ_of_gcd 61 183 244 61 1 3 4 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 60 183 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 183 244 (accept_3_3 59 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 183 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 183 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 244 (accept_3_3 56 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 183 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 183 244 (accept_3_3 53 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 183 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 183 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 244 (accept_3_3 50 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 244
  (Polychromatic418967fa.accept_13_9_1_10_1_647 48 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 183 244 (accept_3_3 47 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 183 244 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 183 244 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 244 (accept_3_3 44 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 183 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 244 (accept_3_3 41 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 244 (accept_3_3 38 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 183 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 244
  (Polychromatic418967fa.accept_17_2_13_6_1_3772 36 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 244 (accept_3_3 35 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 244 (accept_3_3 32 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 244 (accept_3_3 29 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 244 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 244 (accept_3_3 26 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 244 (accept_3_3 23 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 244 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 244 (accept_3_3 20 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 244 (accept_3_3 17 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 244 (accept_3_3 14 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 244 (accept_3_3 11 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 244 (Polychromatic418967fa.accept_25_10_8_19_1_14736 10 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 244 (accept_3_3 8 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 244 (accept_3_3 5 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 183 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 244 (accept_3_3 2 183 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 182 244 (Eq.refl Bool.true)
  (allA_of_3_1 63 182 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 181 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 181 244 (accept_3_3 62 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 181 244 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 244
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 181 244 (accept_3_3 59 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 181 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 181 244 (accept_3_3 56 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 181 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  55 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 181 244
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 181 244 (accept_3_3 53 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 181 244 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 244 (accept_3_3 50 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 244 (Polychromatic418967fa.accept_8_1_5_4_1_388
  49 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 244
  (Polychromatic418967fa.accept_13_9_12_10_1_242 48 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 181 244 (accept_3_3 47 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 181 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 181 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 244 (accept_3_3 44 181 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 244 (Polychromatic418967fa.accept_19_5_10_16_1_6507 43 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 244
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 181 244 (accept_3_3 41 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 181 244 (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 181 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 244 (accept_3_3 38 181 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 244
  (Polychromatic418967fa.accept_24_12_13_4_1_14735 36 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 181 244 (accept_3_3 35 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 181 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 244 (accept_3_3 32 181 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 244
  (Polychromatic418967fa.accept_16_15_5_4_1_6678 31 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 181 244 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 244 (accept_3_3 29 181 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 181 244 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 244 (accept_3_3 26 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 244 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 244 (accept_3_3 23 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 181
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 244 (accept_3_3 20 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 244 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 244 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 244 (accept_3_3 17 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 244 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 181
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 244 (accept_3_3 14 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 244 (Polychromatic418967fa.accept_17_13_11_6_1_4837 13 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 244 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 244 (accept_3_3 11 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 181
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 244 (accept_3_3 8 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 244 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 244 (accept_3_3 5 181 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 244 (Polychromatic418967fa.accept_17_4_11_6_1_3730 4 181
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 244 (accept_3_3 2 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 180 244
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 180 244 4 16 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 244 (Polychromatic418967fa.accept_17_12_10_6_1_3691 63 180
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 180 244 2 31 90 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 244
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 244 4 15 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 244 (accept_3_3 59 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 180 244 2 29 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 180 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 180 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 180 244 4 14 45 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 244
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 55 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 180 244 2 27 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 244 (accept_3_3 53 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 180 244 4 13 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 180 244 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 180 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 180 244 2 25 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 244
  (Polychromatic418967fa.accept_22_5_4_2_1_6803 49 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 244 4 12 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 244 (accept_3_3 47 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 180 244 2 23 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 180 244 (Polychromatic418967fa.accept_19_7_9_16_1_10774 45 180 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 180 244 4 11 45 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 244 2 21 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 244 (accept_3_3 41 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 244 4 10 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 180 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 244 2 19 90 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 244
  (Polychromatic418967fa.accept_19_18_9_16_1_6524 37 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 180 244 4 9 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 180 244 (accept_3_3 35 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 180 244 2 17 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 180 244 (Polychromatic418967fa.accept_17_16_10_6_1_7313 33 180 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 244 4 8 45 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 244
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 244 2 15 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 244 (accept_3_3 29 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 244 4 7 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 180 244 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 180 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 244 2 13 90 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 244 4 6 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 244 (accept_3_3 23 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  180 244 2 11 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 180 244 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 180 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 244 4 5 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 244
  (Polychromatic418967fa.accept_24_19_12_4_1_13043 19 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 244 2 9 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 244 (accept_3_3 17 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 244 4 4 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 180 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 180 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 244 2 7 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 244
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 244 4 3 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 244 (accept_3_3 11 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 244 2 5 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 180 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 244 4 2 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 244 (Polychromatic418967fa.accept_19_7_9_16_1_10774
  7 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 244 2 3 90 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 244 (accept_3_3 5
  180 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 244 4 1 45 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 244
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 180 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 244 2 1 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 180 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 66 179 244 (Eq.refl Bool.true) (allA_of_3_1 66 179 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 67 178 244 (Eq.refl Bool.true) (allA_succ_of_gcd 66 178 244 2 33 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 178 244 (accept_3_3 65 178 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 178 244 2 32 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 178 244 (Polychromatic418967fa.accept_19_6_7_16_1_1418
  63 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 244 2 31 89 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 244 2 30 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 244 (accept_3_3 59 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 244 2 29 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 244 2 28 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 244 2 27 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 244 (accept_3_3 53 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 244 2 26 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 244 2 25 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 244 2 24 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 244 (accept_3_3 47 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 244 2 23 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 244 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 178 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 244 2 22 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 244 2 21 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 244 (accept_3_3 41 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 244 2 20 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 244 2 19 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 244 2 18 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 244 (accept_3_3 35 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 244 2 17 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 244 2 16 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 244 2 15 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 244 (accept_3_3 29 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 244 2 14 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 178 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 244 2 13 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 244 2 12 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 244 (accept_3_3 23 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 244 2 11 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 244 2 10 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 244
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 244 2 9 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 244 (accept_3_3 17 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 244 2 8 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 244 2 7 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 244 2 6 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 244 (accept_3_3 11 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 244 2 5 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 178 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 244 2 4 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 244 2 3 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 244 (accept_3_3 5 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  244 2 2 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 178 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 244 2 1 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 244 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 178 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 177 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 177 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 177 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 177 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 177 244 (accept_3_3 65 177 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 64
  177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 244
  (Polychromatic418967fa.accept_10_3_7_4_1_584 63 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 177 244 (accept_3_3 62 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 177 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 244 (accept_3_3 59 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 177 244 (accept_3_3 56 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 177 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 244 (accept_3_3 53 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 177 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 244
  (Polychromatic418967fa.accept_10_1_7_4_1_968 51 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 177 244 (accept_3_3 50 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 177 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 244 (accept_3_3 47 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 177 244 (accept_3_3 44 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 177 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 244 (accept_3_3 41 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 177 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 177 244 (accept_3_3 38 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 177 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 244 (accept_3_3 35 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 244
  (Polychromatic418967fa.accept_10_3_7_4_1_584 33 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 244 (accept_3_3 32 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 244 (accept_3_3 29 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 244 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 177 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 244
  (Polychromatic418967fa.accept_18_9_15_10_1_395 27 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 244 (accept_3_3 26 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 244 (accept_3_3 23 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 244
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 244 (accept_3_3 20 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 244 (accept_3_3 17 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 244 (accept_3_3 14 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 244 (accept_3_3 11 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 244
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 244 (accept_3_3 8 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 244 (accept_3_3 5 177 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 244 (accept_3_3 2 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 176
  244 (Eq.refl Bool.true) (allA_of_3_1 69 176 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 175 244
  (Eq.refl Bool.true) (allA_succ_of_accept 69 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 244 (accept_3_3 68 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 175 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 175 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 175 244 (accept_3_3 65 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 175 244 (Polychromatic418967fa.accept_13_12_6_10_1_667 64 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 244 (accept_3_3 62 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 175 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 175 244 (accept_3_3 59 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 175 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 244 (accept_3_3 56 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 175 244 (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 175 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 244
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 244 (accept_3_3 53 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 244 (accept_3_3 50 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 175 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 175 244 (accept_3_3 47 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 175 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 244 (accept_3_3 44 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 244 (accept_3_3 41 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 244 (Polychromatic418967fa.accept_16_8_15_4_1_5402 40 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 244 (accept_3_3 38 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 244 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 244 (accept_3_3 35 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 244 (accept_3_3 32 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 244 (accept_3_3 29 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 244 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 244 (accept_3_3 26 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 244 (accept_3_3 23 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 244 (accept_3_3 20 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 244
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 244 (accept_3_3 17 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 244 (accept_3_3 14 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 244 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 175 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 244 (accept_3_3 11 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 244 (accept_3_3 8 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 244 (accept_3_3 5 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 244 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 175 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 244 (accept_3_3 2 175 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 175 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 174 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 174 244 2 35 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 174 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 174 244 2 34 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 244 2 33 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 244 (accept_3_3 65 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 174 244 2 32 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 174 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 174 244 2 31 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 244 2 30 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 244 (accept_3_3 59 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 174 244 2 29 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 174 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 174 244 2 28 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 244
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 55 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 244 2 27 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 244 (accept_3_3 53 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 174 244 2 26 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 174 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 174 244 2 25 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 244 2 24 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 244 (accept_3_3 47 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 244 2 23 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 244 2 22 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 244 2 21 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 244 (accept_3_3 41 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 244 2 20 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 244 2 19 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 244
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 244 2 18 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 244 (accept_3_3 35 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 244 2 17 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 244 2 16 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 244 2 15 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 244 (accept_3_3 29 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 244 2 14 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 244 2 13 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 244 2 12 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 244 (accept_3_3 23 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 244 2 11 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 244 2 10 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 244
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 244 2 9 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 244 (accept_3_3 17 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 244 2 8 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 244 2 7 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 244 2 6 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 244 (accept_3_3 11 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 244 2 5 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 174 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 244 2 4 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 244 2 3 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 244 (accept_3_3 5 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  244 2 2 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 174 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 244 2 1 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 244 (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 174 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 173 244 (Eq.refl Bool.true)
  (allA_of_3_1 72 173 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 172 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 172 244 4 18 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 244 (accept_3_3 71 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 244 2 35 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 244 (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 172 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 244 4 17 43 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 67 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 244 2 33 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 244 (accept_3_3 65 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 244 4 16 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 244 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 172 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 244 2 31 86 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 244 4 15 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 244 (accept_3_3 59 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 244 2 29 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 172 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 244 4 14 43 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 244
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 244 2 27 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 244 (accept_3_3 53 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 244 4 13 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 172 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 244 2 25 86 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 244
  (Polychromatic418967fa.accept_16_1_12_4_1_695 49 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 244 4 12 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 244 (accept_3_3 47 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 244 2 23 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 172 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 244 4 11 43 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 244
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 43 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 172 244 2 21 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 172 244 (accept_3_3 41 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 244 4 10 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 244 (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 172 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 244 2 19 86 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 244 4 9 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 244 (accept_3_3 35 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 244 2 17 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 172 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 244 4 8 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 31
  172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 244 2 15 86 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 244 (accept_3_3 29
  172 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 244 4 7 43 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 244 2 13 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 172 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 244 4 6 43 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 244 (accept_3_3 23 172 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 244 2 11 86 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 244
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 244 4 5 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 172 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 244 2 9 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 244 (accept_3_3 17 172 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 244 4 4 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 244 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 172
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 244 2 7 86 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 244
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 172 244 4 3 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 172 244 (accept_3_3 11 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 244 2 5 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 244 4 2 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 7
  172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 244 2 3 86 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 244 (accept_3_3 5
  172 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 244 4 1 43 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 172 244 2 1 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 172 244 (Polychromatic418967fa.accept_16_1_12_4_1_695 1 172 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 172
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 171 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 171 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 171 244 (accept_3_3 71
  171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 244
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 171 244 (Polychromatic418967fa.accept_15_9_6_4_1_1220 69 171 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 244 (accept_3_3 68 171 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 171 244 (Polychromatic418967fa.accept_12_6_3_4_1_394
  66 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 244 (accept_3_3 65
  171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 244
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 64 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 171 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 244 (accept_3_3 62 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 171 244 (accept_3_3 59 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 171 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 171 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 244 (accept_3_3 56 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 244 (accept_3_3 53 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 171 244 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 244 (accept_3_3 50 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 244
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 244 (accept_3_3 47 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 244 (accept_3_3 44 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 244 (accept_3_3 41 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 244 (Polychromatic418967fa.accept_15_10_6_4_1_1256 40 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 244 (accept_3_3 38 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 244
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 36 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 244 (accept_3_3 35 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 244 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 244 (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 244 (accept_3_3 32 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 244 (accept_3_3 29 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 244 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 244 (accept_3_3 26 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 244
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 244 (accept_3_3 23 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 244 (Polychromatic418967fa.accept_16_6_11_4_1_635 22 171 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 244 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 171
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 244 (accept_3_3 20 171
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  19 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 244 (accept_3_3 17 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 244 (accept_3_3 14 171 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 244
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 244 (accept_3_3 11 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 244 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 171 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 244 (accept_3_3 8 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 244 (accept_3_3 5 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 244 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 244 (accept_3_3 2 171 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 170 244 (Eq.refl
  Bool.true) (allA_of_3_1 75 170 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 169 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 169 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 169 244 (accept_3_3 74 169 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 169 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 73 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 169 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 169 244 (accept_3_3 71 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 169 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 244 (accept_3_3 68 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 244 (accept_3_3 65 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 244 (accept_3_3 62 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 244 (accept_3_3 59 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 244 (accept_3_3 56 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 55 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 244 (accept_3_3 53 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 244 (Polychromatic418967fa.accept_19_14_17_16_1_1434 52 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 244 (accept_3_3 50 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 169 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 244 (accept_3_3 47 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 244 (accept_3_3 44 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 244 (accept_3_3 41 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 244 (accept_3_3 38 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 244
  (Polychromatic418967fa.accept_24_12_1_4_1_14734 36 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 169 244 (accept_3_3 35 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 169 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 169 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 244 (accept_3_3 32 169 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 244 (Polychromatic418967fa.accept_9_4_7_1_1_379
  31 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 244 (accept_3_3 29 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 244 (accept_3_3 26 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 244 (accept_3_3 23 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 244 (accept_3_3 20 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 244
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 244 (accept_3_3 17 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 244 (accept_3_3 14 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 244 (accept_3_3 11 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 244 (accept_3_3 8 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 244 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 244 (accept_3_3 5 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 244 (accept_3_3 2 169 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 244 (Polychromatic418967fa.accept_19_1_17_16_1_2578 1 169 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 168 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 168 244 4 19 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 168 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 168 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 168 244 2 37 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 244
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 73 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 168 244 4 18 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 168 244 (accept_3_3 71 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 168 244 2 35 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 168 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 168 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 168 244 4 17 42 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 244 2 33 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 244 (accept_3_3 65 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 168 244 4 16 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 168 244 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 168 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 168 244 2 31 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 244 4 15 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 244 (accept_3_3 59 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 244 2 29 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 168 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 168 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 244 4 14 42 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 244
  (Polychromatic418967fa.accept_16_7_8_4_1_689 55 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 244 2 27 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 244 (accept_3_3 53 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 244 4 13 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 168 244 (Polychromatic418967fa.accept_16_3_8_4_1_3279 51 168 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 244 2 25 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 244 4 12 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 244 (accept_3_3 47 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 244 2 23 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 168 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 244 4 11 42 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 244 2 21 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 244 (accept_3_3 41 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 244 4 10 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 168 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 168 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 244 2 19 84 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 244
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 244 4 9 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 244 (accept_3_3 35 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 244 2 17 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 168 244 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 168 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 244 4 8 42 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 244 2 15 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 244 (accept_3_3 29 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 244 4 7 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 244 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 168 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 244 2 13 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 25
  168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 244 4 6 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 244 (accept_3_3 23
  168 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 244 2 11 84 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 244 4 5 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 168 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 244 2 9 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 244 (accept_3_3 17 168 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 244 4 4 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 244 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 168
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 244 2 7 84 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 244 4 3 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 244 (accept_3_3 11 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  168 244 2 5 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 168 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 168 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 244 4 2 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 244 2 3 84 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 244 (accept_3_3 5
  168 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 244 4 1 42 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 168 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 168 244 2 1 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 168 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 167 244 (Eq.refl
  Bool.true) (allA_of_3_1 78 167 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 166 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 166 244 2 39 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 244 (accept_3_3 77 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 244 2 38 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 244 2 37 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 244 2 36 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 244 (accept_3_3 71 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 244 2 35 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 244 2 34 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 244 2 33 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 244 (accept_3_3 65 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 244 2 32 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 244 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 166 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 244 2 31 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 244 2 30 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 244 (accept_3_3 59 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 244 2 29 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 244 2 28 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 244 2 27 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 244 (accept_3_3 53 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 244 2 26 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 244 2 25 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 244 2 24 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 244 (accept_3_3 47 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 244 2 23 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 244 2 22 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 244 2 21 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 244 (accept_3_3 41 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 244 2 20 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 244 2 19 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 244 2 18 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 244 (accept_3_3 35 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 244 2 17 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 244 2 16 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 244 2 15 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 244 (accept_3_3 29 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 244 2 14 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 244 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 166 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 244 2 13 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 244 2 12 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 244 (accept_3_3 23 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 244 2 11 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 244 2 10 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 244 2 9 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 244 (accept_3_3 17 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 244 2 8 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 166 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 244 2 7 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 244 2 6 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 244 (accept_3_3 11 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 244 2 5 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 244 (Polychromatic418967fa.accept_19_9_14_16_1_3791 9 166 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 244 2 4 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 244 2 3 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 244 (accept_3_3 5 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  244 2 2 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 166 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 244 2 1 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 166 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 165 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 244 (Polychromatic418967fa.accept_9_6_3_1_1_155
  78 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 165 244 (accept_3_3 77
  165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 76 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 165 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 165 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 244 (accept_3_3 74 165 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 244 (Polychromatic418967fa.accept_7_2_4_6_1_166
  72 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 244 (accept_3_3 71
  165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 70 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 165 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 165 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 244 (accept_3_3 68 165 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 244 (Polychromatic418967fa.accept_7_3_4_6_1_329
  66 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 244 (accept_3_3 65
  165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 244
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 64 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 244 (Polychromatic418967fa.accept_16_15_5_4_1_6678 63 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 244 (accept_3_3 62 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 165 244 (accept_3_3 59 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 165 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 165 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 244 (accept_3_3 56 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 244 (accept_3_3 53 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 165 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 244 (accept_3_3 50 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 244
  (Polychromatic418967fa.accept_19_10_13_16_1_10734 48 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 244 (accept_3_3 47 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 165 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 244 (accept_3_3 44 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 244 (accept_3_3 41 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 165 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 244 (accept_3_3 38 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 165 244 (accept_3_3 35 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 165 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 165 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 244 (accept_3_3 32 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 244 (accept_3_3 29 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 244 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 244 (accept_3_3 26 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 244 (accept_3_3 23 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 244 (accept_3_3 20 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 244 (accept_3_3 17 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 244 (accept_3_3 14 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 244 (accept_3_3 11 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 244 (accept_3_3 8 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 244 (accept_3_3 5 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 165 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 244 (accept_3_3 2 165 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 164 244 (Eq.refl
  Bool.true) (allA_of_3_1 81 164 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 163 244 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 163 244 (accept_3_3 80 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 163 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 78
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 244 (accept_3_3 77
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 244
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 76 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 244 (accept_3_3 74 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 163 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 244 (Polychromatic418967fa.accept_16_8_3_4_1_3233
  72 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 244 (accept_3_3 71
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 244
  (Polychromatic418967fa.accept_11_4_9_2_1_259 70 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 244 (accept_3_3 68 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 163 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 66
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 244 (accept_3_3 65
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 244 (accept_3_3 62 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 163 244 (Polychromatic418967fa.accept_19_4_11_16_1_1474 61 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 244 (accept_3_3 59 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 244 (accept_3_3 56 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 244
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 54 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 244 (accept_3_3 53 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 244 (accept_3_3 50 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 244
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 244 (accept_3_3 47 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 244 (accept_3_3 44 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 244
  (Polychromatic418967fa.accept_13_3_7_10_1_668 42 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 244 (accept_3_3 41 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 244 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 244 (accept_3_3 38 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 244 (accept_3_3 35 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 244 (accept_3_3 32 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 244
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 244 (accept_3_3 29 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 244 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 244 (accept_3_3 26 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 244 (accept_3_3 23 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 244 (accept_3_3 20 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 244 (accept_3_3 17 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 244 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 244 (accept_3_3 14 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 244 (Polychromatic418967fa.accept_18_13_1_10_1_4331 13 163 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 244
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 163 244 (accept_3_3 11 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 163 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 163 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 244 (accept_3_3 8 163 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 244
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 6 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 244 (accept_3_3 5 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 244 (accept_3_3 2 163 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 162 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 162 244 2 41 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 162 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 162 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 162 244 2 40 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 244 2 39 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 244 (accept_3_3 77 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 162 244 2 38 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 162 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 162 244 2 37 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 244
  (Polychromatic418967fa.accept_23_4_1_14_1_13200 73 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 162 244 2 36 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 162 244 (accept_3_3 71 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 244 2 35 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 162 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 162 244 2 34 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 67 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 244 2 33 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 244 (accept_3_3 65 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 244 2 32 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 244 2 31 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 244 2 30 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 244 (accept_3_3 59 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 244 2 29 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 244 2 28 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 244
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 244 2 27 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 244 (accept_3_3 53 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 244 2 26 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 244 2 25 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 244
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 244 2 24 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 244 (accept_3_3 47 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 244 2 23 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 244 2 22 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 244
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 244 2 21 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 244 (accept_3_3 41 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 244 2 20 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 244 2 19 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 244 2 18 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 244 (accept_3_3 35 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 244 2 17 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 244 2 16 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 244
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 244 2 15 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 244 (accept_3_3 29 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 244 2 14 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 244 2 13 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 244
  (Polychromatic418967fa.accept_13_12_6_10_1_667 25 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 244 2 12 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 244 (accept_3_3 23 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 244 2 11 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 244 2 10 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 244 2 9 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 244 (accept_3_3 17 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 244 2 8 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 244 2 7 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 244
  (Polychromatic418967fa.accept_19_13_10_16_1_9334 13 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 244 2 6 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 244 (accept_3_3 11 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 244 2 5 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 244 2 4 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 244 2 3 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 244 (accept_3_3 5 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  244 2 2 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 162 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 244 2 1 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 244 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 162 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 161 244 (Eq.refl
  Bool.true) (allA_of_3_1 84 161 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 160 244 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 160 244 4 21 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 160 244 (accept_3_3 83 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 160 244 2 41 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 160 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 244 4 20 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 244
  (Polychromatic418967fa.accept_13_1_4_10_1_622 79 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 160 244 2 39 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 160 244 (accept_3_3 77 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 160 244 4 19 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 160 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 160 244 2 37 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 244
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 73 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 160 244 4 18 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 160 244 (accept_3_3 71 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 160 244 2 35 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 160 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 244 4 17 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 160 244 2 33 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 160 244 (accept_3_3 65 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 160 244 4 16 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 160 244 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 160 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 244 2 31 80 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 244
  (Polychromatic418967fa.accept_22_17_6_2_1_14733 61 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 160 244 4 15 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 160 244 (accept_3_3 59 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 244 2 29 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 244 4 14 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 244
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 55 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 160 244 2 27 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 160 244 (accept_3_3 53 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 244 4 13 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 244 2 25 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 244 4 12 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 244 (accept_3_3 47 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 244 2 23 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 244 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 160 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 244 4 11 40 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 244
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 244 2 21 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 244 (accept_3_3 41 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 244 4 10 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 244 2 19 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 244
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 244 4 9 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 160 244 (accept_3_3 35 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  160 244 2 17 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 160 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 160 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 244 4 8 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 244 2 15 80 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 244 (accept_3_3 29
  160 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 244 4 7 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 244
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 160 244 2 13 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 160 244 (Polychromatic418967fa.accept_19_6_8_16_1_13419 25 160 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 244 4 6 40 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 244 (accept_3_3 23 160 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 244 2 11 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 244 4 5 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 244 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 160 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 244 2 9 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 244 (accept_3_3 17 160 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 244 4 4 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 160 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 244 2 7 80 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 244 4 3 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 244 (accept_3_3 11 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 244 2 5 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 160 244 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 160 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 244 4 2 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 244 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 160 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 244 2 3 80 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 244 (accept_3_3 5
  160 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 244 4 1 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 160 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 244 2 1 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 244 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 160 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 159 244
  (Eq.refl Bool.true) (allA_succ_of_accept 85 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 159 244 (accept_3_3 83 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 159 244 (Polychromatic418967fa.accept_19_6_7_16_1_1418 82 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 244 (accept_3_3 80 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 159 244 (accept_3_3 77 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 159 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 244 (accept_3_3 74 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 244
  (Polychromatic418967fa.accept_13_7_3_10_1_656 72 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 159 244 (accept_3_3 71 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 159 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 159 244 (Polychromatic418967fa.accept_14_13_5_6_1_2747 69 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 244 (accept_3_3 68 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 159 244 (accept_3_3 65 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 159 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 244 (accept_3_3 62 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 244 (accept_3_3 59 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 244 (accept_3_3 56 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 244 (accept_3_3 53 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 244 (accept_3_3 50 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 244 (accept_3_3 47 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 244 (accept_3_3 44 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 244 (accept_3_3 41 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 244 (accept_3_3 38 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 244 (accept_3_3 35 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 244 (accept_3_3 32 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 244 (accept_3_3 29 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 244 (accept_3_3 26 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 244
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 244 (accept_3_3 23 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 159 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 244 (accept_3_3 20 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 244 (accept_3_3 17 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 244 (accept_3_3 14 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 244 (accept_3_3 11 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 244 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 244 (Polychromatic418967fa.accept_18_9_15_10_1_395 9 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 244 (accept_3_3 8 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 244 (accept_3_3 5 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 244 (accept_3_3 2 159 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 158 244
  (Eq.refl Bool.true) (allA_of_3_1 87 158 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 157 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 244 (accept_3_3 86 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 85 157 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 244 (accept_3_3 83 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 82 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 244 (accept_3_3 80 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 244 (accept_3_3 77 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 244 (Polychromatic418967fa.accept_13_11_1_10_1_648 76 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 244 (accept_3_3 74 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 244 (accept_3_3 71 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 244 (accept_3_3 68 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 244 (accept_3_3 65 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 244 (Polychromatic418967fa.accept_21_1_10_13_1_5623 64 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 244 (accept_3_3 62 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 244 (accept_3_3 59 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 244 (accept_3_3 56 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 157 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 244
  (Polychromatic418967fa.accept_16_6_13_4_1_643 54 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 244 (accept_3_3 53 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 244 (accept_3_3 50 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 244 (accept_3_3 47 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 244 (accept_3_3 44 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 244 (accept_3_3 41 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 244 (accept_3_3 38 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 244
  (Polychromatic418967fa.accept_17_2_4_6_1_1619 36 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 244 (accept_3_3 35 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 244 (accept_3_3 32 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 244 (accept_3_3 29 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 244 (Polychromatic418967fa.accept_16_12_13_4_1_3198 28 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 244 (accept_3_3 26 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 244 (accept_3_3 23 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 244 (accept_3_3 20 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 244 (Polychromatic418967fa.accept_17_2_4_6_1_1619 19 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 244 (accept_3_3 17 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 244 (accept_3_3 14 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 244
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 244 (accept_3_3 11 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 244 (accept_3_3 8 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 244 (accept_3_3 5 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 157 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 244 (accept_3_3 2 157 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 157 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 156 244
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 156 244 4 22 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 156 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 156 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 156 244 2 43 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 244 4 21 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 244 (accept_3_3 83 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 244 2 41 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 156 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 156 244 4 20 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 244 2 39 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 244 (accept_3_3 77 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 244 4 19 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 156 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 75 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 156 244 2 37 78 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 244 4 18 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 244 (accept_3_3 71 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 244 2 35 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 244 4 17 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 244 2 33 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 244 (accept_3_3 65 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 244 4 16 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 156 244 (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 156 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 244 2 31 78 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 244 4 15 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 244 (accept_3_3 59 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 244 2 29 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 244 4 14 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 244 2 27 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 244 (accept_3_3 53 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 244 4 13 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 244 2 25 78 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 244 4 12 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 244 (accept_3_3 47 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 244 2 23 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 244 4 11 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 244 2 21 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 244 (accept_3_3 41 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 244 4 10 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 244 2 19 78 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 244
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 37 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 244 4 9 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 244 (accept_3_3 35 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 244 2 17 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 156 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 244 4 8 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 31
  156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 244 2 15 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 244 (accept_3_3 29
  156 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 244 4 7 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 244
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 156 244 2 13 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 156 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 244 4 6 39 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 244 (accept_3_3 23 156 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 244 2 11 78 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 244
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 244 4 5 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 244 (Polychromatic418967fa.accept_16_3_12_4_1_170 19 156 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 244 2 9 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 244 (accept_3_3 17 156 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 244 4 4 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 244 2 7 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 244 4 3 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 244 (accept_3_3 11 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  156 244 2 5 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 156 244 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 156 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 244 4 2 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 244 2 3 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 244 (accept_3_3 5
  156 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 244 4 1 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 244 2 1 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 155 244
  (Eq.refl Bool.true) (allA_of_3_1 90 155 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 154 244 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 154 244 2 45 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 154 244 (accept_3_3 89 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 244 2 44 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 244 (Polychromatic418967fa.accept_17_2_1_6_1_3777 87 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 244 2 43 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 244 2 42 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 244 (accept_3_3 83 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 244 2 41 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 244 (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 244 2 40 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 244 2 39 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 154 244 (accept_3_3 77 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 244 2 38 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 244 (Polychromatic418967fa.accept_19_18_2_16_1_9347 75 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 244 2 37 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 244 2 36 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 244 (accept_3_3 71 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 244 2 35 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 244 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 244 2 34 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 244 2 33 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 244 (accept_3_3 65 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 244 2 32 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 244 (Polychromatic418967fa.accept_17_12_1_6_1_3680 63 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 244 2 31 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 244 2 30 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 244 (accept_3_3 59 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 244 2 29 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 244 (Polychromatic418967fa.accept_21_15_7_13_1_14725 57 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 244 2 28 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 244 2 27 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 244 (accept_3_3 53 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 244 2 26 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 244 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 244 2 25 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 244 2 24 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 244 (accept_3_3 47 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 244 2 23 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 244 (Polychromatic418967fa.accept_19_7_2_16_1_1496 45 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 244 2 22 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 244 2 21 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 244 (accept_3_3 41 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 244 2 20 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 244 (Polychromatic418967fa.accept_17_5_1_6_1_2615 39 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 244 2 19 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 244 2 18 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 244 (accept_3_3 35 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 244 2 17 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 244 (Polychromatic418967fa.accept_19_14_2_16_1_6484 33 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 244 2 16 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 244 2 15 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 244 (accept_3_3 29 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 244 2 14 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 244 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 244 2 13 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 244 2 12 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 244 (accept_3_3 23 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 244 2 11 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 244 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 244 2 10 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 244 2 9 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 244 (accept_3_3 17 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 244 2 8 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 244 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 244 2 7 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 244 2 6 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 244 (accept_3_3 11 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 244 2 5 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 244 (Polychromatic418967fa.accept_20_9_14_4_1_4540 9 154 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 244 2 4 77 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 244 2 3 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 244 (accept_3_3 5 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  244 2 2 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 244 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 154 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 244 2 1 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 244 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 153 244
  (Eq.refl Bool.true) (allA_succ_of_accept 91 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 153 244 (accept_3_3 89 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 153 244 (Polychromatic418967fa.accept_16_8_9_4_1_630 88 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 153 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 87 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 244 (accept_3_3 86 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 244
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 84 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 244 (accept_3_3 83 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 153 244 (Polychromatic418967fa.accept_14_12_13_6_1_1140 82 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 244
  (Polychromatic418967fa.accept_19_5_1_16_1_6501 81 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 153 244 (accept_3_3 80 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 153 244 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 244 (accept_3_3 77 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 244 (Polychromatic418967fa.accept_15_1_3_4_1_1217 76 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 244
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 75 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 153 244 (accept_3_3 74 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 153 244 (Polychromatic418967fa.accept_16_8_9_4_1_630 72 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 244 (accept_3_3 71 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 244 (Polychromatic418967fa.accept_19_13_1_16_1_7979 70 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 244
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 244 (accept_3_3 68 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 244 (accept_3_3 65 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 244 (Polychromatic418967fa.accept_24_16_9_4_1_13069 64 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 244
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 63 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 244 (accept_3_3 62 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 244 (Polychromatic418967fa.accept_16_12_9_4_1_4345 60 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 244 (accept_3_3 59 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 244 (Polychromatic418967fa.accept_21_16_6_13_1_10430 58
  153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 244
  (Polychromatic418967fa.accept_10_7_3_4_1_978 57 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 244 (accept_3_3 56 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 244 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 244 (accept_3_3 53 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 244 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 244
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 51 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 153 244 (accept_3_3 50 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 244 (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 244 (accept_3_3 47 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 244
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 153 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 153 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 244 (accept_3_3 44 153 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 244 (Polychromatic418967fa.accept_12_6_9_4_1_96
  42 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 244 (accept_3_3 41
  153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 244
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 244 (accept_3_3 38 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 244
  (Polychromatic418967fa.accept_19_17_1_16_1_1443 36 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 244 (accept_3_3 35 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 244 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 153 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 244 (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 244 (accept_3_3 32 153
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 244 (accept_3_3 29 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 244 (Polychromatic418967fa.accept_16_12_9_4_1_4345 28 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 244 (accept_3_3 26 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 244
  (Polychromatic418967fa.accept_16_8_9_4_1_630 24 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 244 (accept_3_3 23 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 244 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 244 (accept_3_3 20 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 244 (accept_3_3 17 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 244 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 244 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 244 (accept_3_3 14 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 244
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 244 (accept_3_3 11 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 244 (Polychromatic418967fa.accept_19_10_1_16_1_7977 10 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 244 (accept_3_3 8 153 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 244 (accept_3_3 5 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 244 (Polychromatic418967fa.accept_19_4_1_16_1_13397 4 153 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 244 (Polychromatic418967fa.accept_19_3_1_16_1_7947 3 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 244 (accept_3_3 2 153 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 152 244
  (Eq.refl Bool.true) (allA_of_3_1 93 152 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 151 244 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 151 244 (accept_3_3 92 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 151 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 151 244
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 90 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 151 244 (accept_3_3 89 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 151 244 (Polychromatic418967fa.accept_16_8_7_4_1_2217 88 151 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 151 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 244 (accept_3_3 86 151 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379
  85 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 151 244 (accept_3_3 83 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 151 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 244 (accept_3_3 80 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 244 (accept_3_3 77 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 244 (accept_3_3 74 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 244 (accept_3_3 71 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 244 (accept_3_3 68 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 244 (accept_3_3 65 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 244 (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 244 (accept_3_3 62 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 244 (accept_3_3 59 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 244 (accept_3_3 56 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 244 (accept_3_3 53 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 244 (accept_3_3 50 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 244 (accept_3_3 47 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 244 (accept_3_3 44 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 244 (accept_3_3 41 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 244 (accept_3_3 38 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 244
  (Polychromatic418967fa.accept_19_17_18_16_1_10714 36 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 151 244 (accept_3_3 35 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 151 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 151 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 244 (accept_3_3 32 151 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 244 (Polychromatic418967fa.accept_7_3_4_6_1_329
  31 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 244 (accept_3_3 29 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 244 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 244 (accept_3_3 26 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 244 (accept_3_3 23 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 244 (accept_3_3 20 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 244
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 244 (accept_3_3 17 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 244 (accept_3_3 14 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 244 (accept_3_3 11 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 244 (accept_3_3 8 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 244 (accept_3_3 5 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 244 (accept_3_3 2 151 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 244 (Polychromatic418967fa.accept_20_1_11_4_1_10589 1 151 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 150
  244 (Eq.refl Bool.true) (allA_succ_of_gcd 94 150 244 2 47 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 150 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 150 244 2 46 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 244
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 91 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 244 2 45 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 244 (accept_3_3 89 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 150 244 2 44 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 150 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 150 244 2 43 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 244 2 42 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 244 (accept_3_3 83 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 244 2 41 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 150 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 150 244 2 40 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 244 2 39 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 244 (accept_3_3 77 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 244 2 38 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 150 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 150 244 2 37 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 244
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 244 2 36 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 244 (accept_3_3 71 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 244 2 35 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 244 2 34 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 244 2 33 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 244 (accept_3_3 65 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 244 2 32 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 244 2 31 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 244 2 30 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 244 (accept_3_3 59 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 244 2 29 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 244 2 28 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 244
  (Polychromatic418967fa.accept_13_3_7_10_1_668 55 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 244 2 27 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 244 (accept_3_3 53 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 244 2 26 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 244 2 25 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 244 2 24 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 244 (accept_3_3 47 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 244 2 23 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 244 2 22 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 244 2 21 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 244 (accept_3_3 41 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 244 2 20 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 244 2 19 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 244 2 18 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 244 (accept_3_3 35 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 244 2 17 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 244 2 16 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 244 2 15 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 244 (accept_3_3 29 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 244 2 14 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 244 2 13 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 244 2 12 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 244 (accept_3_3 23 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 244 2 11 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 244 2 10 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 244
  (Polychromatic418967fa.accept_16_3_6_4_1_679 19 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 244 2 9 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 244 (accept_3_3 17 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 244 2 8 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 244 2 7 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 244 2 6 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 244 (accept_3_3 11 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 244 2 5 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 244 2 4 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 244 2 3 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 244 (accept_3_3 5 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  244 2 2 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 244 2 1 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 150 244 (Polychromatic418967fa.accept_19_1_17_16_1_2578 1 150 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 149
  244 (Eq.refl Bool.true) (allA_of_3_1 96 149 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 148 244
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 148 244 4 24 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 148 244 (accept_3_3 95 148 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 148 244 2 47 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 148 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 244 4 23 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 244
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 91 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 244 2 45 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 244 (accept_3_3 89 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 244 4 22 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 87 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 244 2 43 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 244
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 244 4 21 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 244 (accept_3_3 83 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 244 2 41 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 244 (Polychromatic418967fa.accept_15_6_13_4_1_2040 81 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 244 4 20 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 244 2 39 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 244 (accept_3_3 77 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 244 4 19 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 244 2 37 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 244
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 244 4 18 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 244 (accept_3_3 71 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 244 2 35 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 244 4 17 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 244
  (Polychromatic418967fa.accept_13_2_5_10_1_250 67 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 244 2 33 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 244 (accept_3_3 65 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 244 4 16 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 244 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 244 2 31 74 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 244 4 15 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 244 (accept_3_3 59 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 244 2 29 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 244 4 14 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 244
  (Polychromatic418967fa.accept_15_10_13_4_1_1210 55 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 148 244 2 27 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 148 244 (accept_3_3 53 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 244 4 13 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 244 2 25 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 244
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 244 4 12 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 244 (accept_3_3 47 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 244 2 23 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 244 (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 244 4 11 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 244 2 21 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 244 (accept_3_3 41 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 244 4 10 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 244 2 19 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 244 4 9 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 244 (accept_3_3 35 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 244 2 17 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 148 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 244 4 8 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 244
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 31 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 244 2 15 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 244 (accept_3_3 29 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 244 4 7 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 244 (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 244 2 13 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 244 4 6 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 244 (accept_3_3 23 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 244 2 11 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 148 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 244 4 5 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 19
  148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 244 2 9 74 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 244 (accept_3_3 17
  148 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 244 4 4 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 244
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 148 244 2 7 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 148 244 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 244 4 3 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 244 (accept_3_3 11 148 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 244 2 5 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 244 4 2 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 244 2 3 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 244 (accept_3_3 5 148 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 244 4 1 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 148 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 244 2 1 74 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 244
  (Polychromatic418967fa.accept_17_1_12_6_1_3735 1 148 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 147 244 (Eq.refl Bool.true) (allA_succ_of_accept 97 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  97 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 147 244 (accept_3_3 95 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 147 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 93 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 147 244 (accept_3_3 92 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 147 244 (accept_3_3 89 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 147 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 147 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 147 244 (accept_3_3 86 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 244
  (Polychromatic418967fa.accept_13_6_4_10_1_660 84 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 147 244 (accept_3_3 83 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 147 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 82 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 147 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 244 (accept_3_3 80 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 147 244 (accept_3_3 77 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 147 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 244 (accept_3_3 74 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 244
  (Polychromatic418967fa.accept_10_2_7_4_1_967 72 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 147 244 (accept_3_3 71 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 147 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 147 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 244 (accept_3_3 68 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 244 (accept_3_3 65 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 244 (accept_3_3 62 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 244 (accept_3_3 59 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 147 244 (Polychromatic418967fa.accept_13_5_4_10_1_1244 57 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 244 (accept_3_3 56 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 244 (accept_3_3 53 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 244 (accept_3_3 50 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 244
  (Polychromatic418967fa.accept_25_23_22_19_1_14732 48 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 244 (accept_3_3 47 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 244 (Polychromatic418967fa.accept_13_7_4_10_1_2675 46 147 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 244 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 147
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 244 (accept_3_3 44 147
  244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 147 244 (accept_3_3 41 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 147 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 244 (accept_3_3 38 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 244
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 147 244 (accept_3_3 35 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 147 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 147 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 244 (accept_3_3 32 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 244 (accept_3_3 29 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 244 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 244 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 244 (accept_3_3 26 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 244 (accept_3_3 23 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 244 (accept_3_3 20 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 244 (accept_3_3 17 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 244 (accept_3_3 14 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 244
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 244 (accept_3_3 11 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 244 (Polychromatic418967fa.accept_27_10_12_1_1_14731 10 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 244 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 244 (accept_3_3 8 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 244 (accept_3_3 5 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 244 (accept_3_3 2 147 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  146 244 (Eq.refl Bool.true) (allA_of_3_1 99 146 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 145 244
  (Eq.refl Bool.true) (allA_succ_of_accept 99 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 244 (accept_3_3 98 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 244 (Polychromatic418967fa.accept_13_6_2_10_1_1240 97 145
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 96 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 145 244 (accept_3_3 95 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 244 (accept_3_3 92 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 91 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 145 244
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 90 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 145 244 (accept_3_3 89 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 145 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 145 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 244 (accept_3_3 86 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 145 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 85
  145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 244
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 84 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 145 244 (accept_3_3 83 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 244 (accept_3_3 80 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 145 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 79 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 145 244 (accept_3_3 77 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 145 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 76 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 244 (accept_3_3 74 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 244 (Polychromatic418967fa.accept_13_8_2_10_1_652 73 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 244
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 72 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 244 (accept_3_3 71 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 244 (accept_3_3 68 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 66 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 244 (accept_3_3 65 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 244 (accept_3_3 62 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 244 (accept_3_3 59 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 244 (accept_3_3 56 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 244 (Polychromatic418967fa.accept_13_3_2_10_1_2697 55 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 244
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 244 (accept_3_3 53 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 244 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 244 (accept_3_3 50 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 244
  (Polychromatic418967fa.accept_21_6_19_13_1_7196 48 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 145 244 (accept_3_3 47 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 145 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 145 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 244 (accept_3_3 44 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 43
  145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 244
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 244 (accept_3_3 41 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 244 (Polychromatic418967fa.accept_16_8_1_4_1_6622 40 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 244 (accept_3_3 38 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 244 (accept_3_3 35 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 244 (accept_3_3 32 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 244
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 244 (accept_3_3 29 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 244 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 244 (accept_3_3 26 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 244
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 244 (accept_3_3 23 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 145 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 244 (accept_3_3 20 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 244 (Polychromatic418967fa.accept_10_9_5_4_1_966
  19 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 244 (accept_3_3 17 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 244 (accept_3_3 14 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 244
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 145 244 (accept_3_3 11 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 145 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 145 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 244 (accept_3_3 8 145 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 244 (Polychromatic418967fa.accept_15_7_10_4_1_151
  7 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 244 (accept_3_3 5 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 145 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 244 (accept_3_3 2 145 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 144 244 (Eq.refl Bool.true) (allA_succ_of_gcd 100 144 244 4 25 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 244 (Polychromatic418967fa.accept_17_14_8_6_1_2643
  99 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 144 244 2 49 72 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 244
  (Polychromatic418967fa.accept_19_2_11_16_1_6525 97 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 144 244 4 24 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 144 244 (accept_3_3 95 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 244 2 47 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 144 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 144 244 4 23 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 244
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 244 2 45 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 244 (accept_3_3 89 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 244 4 22 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 144 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 144 244 2 43 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 244
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 85 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 244 4 21 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 244 (accept_3_3 83 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 244 2 41 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 144 244 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 144 244 4 20 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 244 2 39 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 244 (accept_3_3 77 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 244 4 19 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 144 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 244 2 37 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 244 4 18 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 244 (accept_3_3 71 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 244 2 35 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 244 (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 244 4 17 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 244
  (Polychromatic418967fa.accept_21_4_18_13_1_10435 67 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 144 244 2 33 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 144 244 (accept_3_3 65 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 244 4 16 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 144 244 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 244 2 31 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 244 4 15 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 244 (accept_3_3 59 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 244 2 29 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 144 244 (Polychromatic418967fa.accept_15_12_9_4_1_3898 57 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 244 4 14 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 244
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 55 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 244 2 27 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 244 (accept_3_3 53 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 244 4 13 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 244 2 25 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 244
  (Polychromatic418967fa.accept_17_15_8_6_1_8733 49 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 244 4 12 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 244 (accept_3_3 47 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 244 2 23 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 244 4 11 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 244
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 244 2 21 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 244 (accept_3_3 41 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 244 4 10 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 244 (Polychromatic418967fa.accept_26_13_14_10_1_14730 39 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 244 2 19 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 244 4 9 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 244 (accept_3_3 35 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  144 244 2 17 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 144 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 244 4 8 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 31
  144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 244 2 15 72 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 244 (accept_3_3 29
  144 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 244 4 7 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 244
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 244 2 13 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 244 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 144 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 244 4 6 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 244 (accept_3_3 23 144 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 244 2 11 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 244
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 244 4 5 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 244 2 9 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 244 (accept_3_3 17 144 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 244 4 4 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 244 (Polychromatic418967fa.accept_17_15_8_6_1_8733 15 144
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 244 2 7 72 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 244
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 244 4 3 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 244 (accept_3_3 11 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  144 244 2 5 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 244 4 2 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 244 (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 144
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 244 2 3 72 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 244 (accept_3_3 5
  144 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 244 4 1 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 244 2 1 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 244 (Polychromatic418967fa.accept_22_1_12_2_1_11707 1 144 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 143 244 (Eq.refl Bool.true) (allA_of_3_1 102 143 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 142
  244 (Eq.refl Bool.true) (allA_succ_of_gcd 102 142 244 2 51 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 142 244 (accept_3_3 101 142 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 142 244 2 50 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 142 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 142 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 244 2 49 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 97 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 244 2 48 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 244 (accept_3_3 95 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 244 2 47 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 244 2 46 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 244 2 45 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 244 (accept_3_3 89 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 244 2 44 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 244 2 43 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 244 2 42 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 244 (accept_3_3 83 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 244 2 41 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 244 2 40 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 244 2 39 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 244 (accept_3_3 77 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 244 2 38 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 244 2 37 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 244 2 36 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 244 (accept_3_3 71 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 244 2 35 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 244 2 34 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 244 2 33 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 244 (accept_3_3 65 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 244 2 32 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 244 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 142 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 244 2 31 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 244 2 30 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 244 (accept_3_3 59 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 244 2 29 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 244 2 28 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 244 2 27 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 244 (accept_3_3 53 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 244 2 26 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 244 2 25 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 244 2 24 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 244 (accept_3_3 47 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 244 2 23 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 244 2 22 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 244 2 21 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 244 (accept_3_3 41 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 244 2 20 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 244 2 19 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 244 2 18 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 244 (accept_3_3 35 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 244 2 17 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 244 2 16 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 244 2 15 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 244 (accept_3_3 29 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 244 2 14 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 244 2 13 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 244 2 12 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 244 (accept_3_3 23 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 244 2 11 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 244 2 10 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 244 2 9 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 244 (accept_3_3 17 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 244 2 8 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 244 2 7 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 244 2 6 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 244 (accept_3_3 11 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 244 2 5 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 244 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 142 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 244 2 4 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 244 2 3 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 244 (accept_3_3 5 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  244 2 2 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 244 2 1 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 142 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 141 244 (Eq.refl Bool.true) (allA_succ_of_accept 103 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 141 244 (accept_3_3 101 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 141 244 (Polychromatic418967fa.accept_13_8_11_10_1_636 99 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 244 (accept_3_3 98 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 141 244 (accept_3_3 95 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 141 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 244 (accept_3_3 92 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 244 (accept_3_3 89 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 87 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 244 (accept_3_3 86 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 244 (accept_3_3 83 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 244 (accept_3_3 80 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 244 (accept_3_3 77 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 244 (accept_3_3 74 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 244 (accept_3_3 71 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 244 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 244 (accept_3_3 68 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 244 (accept_3_3 65 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 244 (Polychromatic418967fa.accept_13_12_11_10_1_2711 64 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 244 (Polychromatic418967fa.accept_14_7_1_6_1_3514 63 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 244 (accept_3_3 62 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 244
  (Polychromatic418967fa.accept_13_8_11_10_1_636 60 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 244 (accept_3_3 59 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 244 (accept_3_3 56 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 244 (accept_3_3 53 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 244 (accept_3_3 50 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 244 (accept_3_3 47 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 244 (Polychromatic418967fa.accept_25_21_16_19_1_14729 46 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 244 (accept_3_3 44 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 244 (accept_3_3 41 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 244 (accept_3_3 38 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 244
  (Polychromatic418967fa.accept_19_17_8_16_1_12029 36 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 244 (accept_3_3 35 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 141 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 244 (accept_3_3 32 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 244
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 244 (accept_3_3 29 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 244 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 244 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 244 (accept_3_3 26 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 244
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 244 (accept_3_3 23 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 244 (accept_3_3 20 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 244
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 244 (accept_3_3 17 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 244 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 244 (accept_3_3 14 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 244 (accept_3_3 11 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 244 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 244 (accept_3_3 8 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 244 (accept_3_3 5 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 244 (accept_3_3 2 141 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 140 244 (Eq.refl Bool.true) (allA_of_3_1 105 140 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 139 244 (Eq.refl Bool.true) (allA_succ_of_accept 105 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 244 (accept_3_3 104 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 103 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 244 (accept_3_3 101 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 244 (Polychromatic418967fa.accept_26_22_9_10_1_14728 100
  139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 244 (accept_3_3 98 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 244 (accept_3_3 95 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 244 (accept_3_3 92 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 244 (Polychromatic418967fa.accept_14_7_13_6_1_1177 91 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 244 (Polychromatic418967fa.accept_13_12_9_10_1_1223 90 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 244 (accept_3_3 89 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 244 (accept_3_3 86 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 85 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 244 (accept_3_3 83 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 244 (accept_3_3 80 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 244 (accept_3_3 77 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 244 (Polychromatic418967fa.accept_16_12_11_4_1_1359 76 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 244 (accept_3_3 74 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 73 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 244 (Polychromatic418967fa.accept_16_8_11_4_1_3290 72 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 244 (accept_3_3 71 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 244 (accept_3_3 68 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 244 (Polychromatic418967fa.accept_19_10_6_16_1_7964 67 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 244 (accept_3_3 65 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 244 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 244 (accept_3_3 62 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 244 (accept_3_3 59 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 58 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 244 (accept_3_3 56 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 244 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 244 (accept_3_3 53 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 244 (accept_3_3 50 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 244 (Polychromatic418967fa.accept_14_7_13_6_1_1177 49 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 244 (accept_3_3 47 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 244 (accept_3_3 44 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 244 (accept_3_3 41 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 244 (accept_3_3 38 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 244 (Polychromatic418967fa.accept_18_1_13_10_1_2024 37 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 244 (Polychromatic418967fa.accept_23_13_1_14_1_11554 36 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 244 (accept_3_3 35 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 244 (accept_3_3 32 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 244 (accept_3_3 29 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 244 (accept_3_3 26 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 244 (accept_3_3 23 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 244 (accept_3_3 20 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 244 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 244 (accept_3_3 17 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 244 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 244 (accept_3_3 14 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 244 (accept_3_3 11 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 244 (accept_3_3 8 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 244 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 244 (accept_3_3 5 139 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 244 (Polychromatic418967fa.accept_18_4_13_10_1_2064 4 139 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 244 (accept_3_3 2 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 139 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 138 244 (Eq.refl Bool.true) (allA_succ_of_gcd 106 138 244 2 53 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 138 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 105 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 138 244 2 52 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 138 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 138 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 138 244 2 51 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 244 (accept_3_3 101 138 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 244 2 50 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 138 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 138 244 2 49 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 138 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 138 244 2 48 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 138 244 (accept_3_3 95 138 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 244 2 47 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 244 (Polychromatic418967fa.accept_12_9_6_4_1_402
  93 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 138 244 2 46 69 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 244
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 91 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 244 2 45 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 244 (accept_3_3 89 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 138 244 2 44 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 138 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 244 2 43 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 244 2 42 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 244 (accept_3_3 83 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 244 2 41 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 244 2 40 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 244 2 39 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 244 (accept_3_3 77 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 244 2 38 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 244 2 37 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 244
  (Polychromatic418967fa.accept_25_23_13_19_1_13004 73 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 138 244 2 36 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 138 244 (accept_3_3 71 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 244 2 35 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 244 2 34 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 244 2 33 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 244 (accept_3_3 65 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 244 2 32 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 244 2 31 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 244 2 30 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 244 (accept_3_3 59 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 244 2 29 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 244 2 28 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 244
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 55 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 138 244 2 27 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 138 244 (accept_3_3 53 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 244 2 26 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 244 2 25 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 244 2 24 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 244 (accept_3_3 47 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 244 2 23 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 244 2 22 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 244 2 21 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 244 (accept_3_3 41 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 244 2 20 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 244 2 19 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 244
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 244 2 18 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 244 (accept_3_3 35 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 244 2 17 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 244 2 16 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 244 2 15 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 244 (accept_3_3 29 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 244 2 14 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 244 2 13 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 244 2 12 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 244 (accept_3_3 23 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 244 2 11 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 244 2 10 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 244
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 244 2 9 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 244 (accept_3_3 17 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 244 2 8 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 244 2 7 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 244
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 244 2 6 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 244 (accept_3_3 11 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 244 2 5 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 244 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 138 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 244 2 4 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 244
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 244 2 3 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 244 (accept_3_3 5 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  244 2 2 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 138 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 244 2 1 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 138 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 137 244 (Eq.refl Bool.true) (allA_of_3_1 108 137 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 136 244 (Eq.refl Bool.true) (allA_succ_of_gcd 108 136 244 4 27 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 136 244 (accept_3_3 107 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 136 244 2 53 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 136 244 (Polychromatic418967fa.accept_10_5_6_4_1_64
  105 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 136 244 4 26 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 136 244
  (Polychromatic418967fa.accept_13_12_6_10_1_667 103 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 136 244 2 51 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 136 244 (accept_3_3 101 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 136 244 4 25 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 136 244 (Polychromatic418967fa.accept_16_3_8_4_1_3279 99 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 136 244 2 49 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 136 244
  (Polychromatic418967fa.accept_11_9_4_2_1_600 97 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 136 244 4 24 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 136 244 (accept_3_3 95 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 136 244 2 47 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 136 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 136 244 4 23 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 136 244
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 91 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 136 244 2 45 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 136 244 (accept_3_3 89 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 136 244 4 22 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 244 (Polychromatic418967fa.accept_13_9_6_10_1_666 87 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 136 244 2 43 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 136 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 85 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 136 244 4 21 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 244 (accept_3_3 83 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 244 2 41 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 244 4 20 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 244 2 39 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 244 (accept_3_3 77 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 244 4 19 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 75 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 244 2 37 68 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 244
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 73 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 244 4 18 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 136 244 (accept_3_3 71 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 244 2 35 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 244 (Polychromatic418967fa.accept_13_4_6_10_1_1199 69 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 244 4 17 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 244 2 33 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 244 (accept_3_3 65 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 244 4 16 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 244 (Polychromatic418967fa.accept_15_3_1_4_1_1246 63 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 244 2 31 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 244
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 244 4 15 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 244 (accept_3_3 59 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 244 2 29 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 244 (Polychromatic418967fa.accept_13_5_6_10_1_2659 57 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 244 4 14 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 244 2 27 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 244 (accept_3_3 53 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 244 4 13 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 244 2 25 68 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 244
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 244 4 12 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 244 (accept_3_3 47 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 244 2 23 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 244 4 11 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 244
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 244 2 21 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 244 (accept_3_3 41 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 244 4 10 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 244 2 19 68 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 244 4 9 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 136 244 (accept_3_3 35 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  136 244 2 17 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 136 244 (Polychromatic418967fa.accept_15_3_1_4_1_1246 33 136 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 244 4 8 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 244 (Polychromatic418967fa.accept_11_9_4_2_1_600
  31 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 244 2 15 68 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 244
  (accept_3_3 29 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 244 4 7 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 244
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 136 244 2 13 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 136 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 244 4 6 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 244 (accept_3_3 23 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 244 2 11 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 244 (Polychromatic418967fa.accept_16_5_8_4_1_5418
  21 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 244 4 5 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 244
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 244 2 9 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 244 (accept_3_3 17 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 244 4 4 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 136 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 244 2 7 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 244 (Polychromatic418967fa.accept_16_13_8_4_1_3250
  13 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 244 4 3 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 244
  (accept_3_3 11 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 244 2 5 68 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 244 4 2 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 244 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 136 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 244 2 3 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 244 (accept_3_3 5 136 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 244 4 1 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 244 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 136 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 244 2 1 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 244
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 136 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 135 244 (Eq.refl Bool.true) (allA_succ_of_accept 109 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  109 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 135 244 (accept_3_3 107 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 135 244 (Polychromatic418967fa.accept_18_15_9_10_1_1082 105 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 135 244 (accept_3_3 104 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 135 244 (accept_3_3 101 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 135 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 100 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 244 (accept_3_3 98 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 96 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 135 244 (accept_3_3 95 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 135 244 (Polychromatic418967fa.accept_13_2_5_10_1_250 93 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 244 (accept_3_3 92 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 135 244 (accept_3_3 89 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 135 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 244 (accept_3_3 86 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 244
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 84 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 244 (accept_3_3 83 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 244 (Polychromatic418967fa.accept_13_4_5_10_1_1247 82 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 244 (accept_3_3 80 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 244 (accept_3_3 77 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 135 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 76 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 244 (accept_3_3 74 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 244
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 244 (accept_3_3 71 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 135 244 (Polychromatic418967fa.accept_19_13_2_16_1_1497 70 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 69 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 244 (accept_3_3 68 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 244 (accept_3_3 65 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 244 (Polychromatic418967fa.accept_22_19_3_2_1_14727 63 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 244 (accept_3_3 62 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 244 (accept_3_3 59 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 244 (Polychromatic418967fa.accept_13_6_5_10_1_1213 58 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 244 (accept_3_3 56 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 244 (accept_3_3 53 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 244 (accept_3_3 50 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 244
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 244 (accept_3_3 47 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 135 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 244 (accept_3_3 44 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 244 (accept_3_3 41 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 244 (Polychromatic418967fa.accept_16_8_7_4_1_2217 40 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 244 (accept_3_3 38 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 244
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 244 (accept_3_3 35 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 244 (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 244 (accept_3_3 32 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 244
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 244 (accept_3_3 29 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 244 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 244 (accept_3_3 26 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 244
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 244 (accept_3_3 23 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 244 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 244 (accept_3_3 20 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 244
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 244 (accept_3_3 17 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 244 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 244 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 244 (accept_3_3 14 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 244
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 244 (accept_3_3 11 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 244 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 244 (accept_3_3 8 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 244
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 244 (accept_3_3 5 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 244 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 244 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 244 (accept_3_3 2 135 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 134 244 (Eq.refl Bool.true) (allA_of_3_1 111 134 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 133 244 (Eq.refl Bool.true) (allA_succ_of_accept 111 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 133 244 (accept_3_3 110 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 133 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 109 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 244 (Polychromatic418967fa.accept_16_12_5_4_1_3275 108 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 244 (accept_3_3 107 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 133
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 244 (accept_3_3 104 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 244 (accept_3_3 101 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 244 (Polychromatic418967fa.accept_15_10_13_4_1_1210 100
  133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 244 (accept_3_3 98 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 97 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 96 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 244 (accept_3_3 95 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 244 (accept_3_3 92 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 244 (Polychromatic418967fa.accept_11_3_1_2_1_1063 91 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 244 (Polychromatic418967fa.accept_21_6_7_13_1_7199 90 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 244 (accept_3_3 89 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 244 (Polychromatic418967fa.accept_16_8_5_4_1_674 88 133
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 244 (accept_3_3 86 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 244 (accept_3_3 83 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 244 (accept_3_3 80 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 79 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 244 (accept_3_3 77 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 244 (accept_3_3 74 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 244 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 244 (accept_3_3 71 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 133
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 244 (accept_3_3 68 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 244 (accept_3_3 65 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 244 (Polychromatic418967fa.accept_14_8_7_6_1_1159 64 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 244 (accept_3_3 62 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 244 (Polychromatic418967fa.accept_21_19_7_13_1_7189 61 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 244 (accept_3_3 59 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 244 (accept_3_3 56 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 244 (Polychromatic418967fa.accept_14_13_7_6_1_3525 55 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 244 (accept_3_3 53 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 244 (Polychromatic418967fa.accept_21_10_7_13_1_10408 52
  133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 244 (accept_3_3 50 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 244 (accept_3_3 47 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 244 (accept_3_3 44 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 244 (accept_3_3 41 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 244 (accept_3_3 38 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 244 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 244 (accept_3_3 35 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 244 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 244 (accept_3_3 32 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 244 (accept_3_3 29 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 244 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 244 (accept_3_3 26 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 244 (accept_3_3 23 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 244 (accept_3_3 20 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 244 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 244 (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 244 (accept_3_3 17 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 244 (Polychromatic418967fa.accept_21_16_7_13_1_11781 16
  133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 244 (accept_3_3 14 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 244 (accept_3_3 11 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 244 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 133 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 244 (accept_3_3 8 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 244 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 244 (accept_3_3 5 133 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 244 (accept_3_3 2 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 244 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 132 244 (Eq.refl Bool.true) (allA_succ_of_gcd 112 132 244 4 28 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 132 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 111 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 132 244 2 55 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 132 244 (Polychromatic418967fa.accept_13_5_2_10_1_248 109 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 244 4 27 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 244 (accept_3_3 107 132 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 132 244 2 53 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 132 244
  (Polychromatic418967fa.accept_18_15_6_10_1_5590 105 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 132 244 4 26 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 132 244 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 244 2 51 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 244 (accept_3_3 101 132 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 132 244 4 25 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 132 244
  (Polychromatic418967fa.accept_13_8_2_10_1_652 99 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 132 244 2 49 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 132 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 244 4 24 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 244 (accept_3_3 95 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 132 244 2 47 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 132 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 93
  132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 244 4 23 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 244
  (Polychromatic418967fa.accept_15_1_12_4_1_2022 91 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 244 2 45 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 244 (accept_3_3 89 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 244 4 22 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 132 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 87 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 244 2 43 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 244 4 21 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 244 (accept_3_3 83 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 244 2 41 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 244 (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 244 4 20 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 244 2 39 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 244 (accept_3_3 77 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 244 4 19 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 244 2 37 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 244
  (Polychromatic418967fa.accept_13_8_2_10_1_652 73 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 244 4 18 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 244 (accept_3_3 71 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 244 2 35 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 244 (Polychromatic418967fa.accept_15_9_12_4_1_2023 69 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 244 4 17 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 244 2 33 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 244 (accept_3_3 65 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 244 4 16 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 244 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 244 2 31 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 244 4 15 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 244 (accept_3_3 59 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 244 2 29 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 244 4 14 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 244
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 55 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 244 2 27 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 244 (accept_3_3 53 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 244 4 13 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 244 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 244 2 25 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 244 4 12 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 244 (accept_3_3 47 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 244 2 23 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 244 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 132 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 244 4 11 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 244
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 244 2 21 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 244 (accept_3_3 41 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 244 4 10 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 244 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 244 2 19 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 244
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 244 4 9 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 244 (accept_3_3 35 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  132 244 2 17 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 132 244 (Polychromatic418967fa.accept_18_15_6_10_1_5590 33 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 244 4 8 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 244 2 15 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 244 (accept_3_3 29 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 244 4 7 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 244 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 244 2 13 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 25
  132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 244 4 6 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 244 (accept_3_3 23
  132 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 244 2 11 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 244 4 5 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 244 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 132 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 244 2 9 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 244 (accept_3_3 17 132 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 244 4 4 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 244 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 132
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 244 2 7 66 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 244
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 244 4 3 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 244 (accept_3_3 11 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  132 244 2 5 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 244 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 132 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 244 4 2 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 244 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 244 2 3 66 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 244 (accept_3_3 5
  132 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 244 4 1 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 244
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 244 2 1 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 244 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 132 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 131 244 (Eq.refl Bool.true) (allA_of_3_1 114 131 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 130 244 (Eq.refl Bool.true) (allA_succ_of_gcd 114 130 244 2 57 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 130 244 (accept_3_3 113 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 130 244 2 56 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 130 244 (Polychromatic418967fa.accept_9_3_4_1_1_22
  111 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 130 244 2 55 65 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 109 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 244 2 54 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 244 (accept_3_3 107 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 244 2 53 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 130 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 130 244 2 52 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 103 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 130 244 2 51 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 130 244 (accept_3_3 101 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 130 244 2 50 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 130 244 (Polychromatic418967fa.accept_15_9_10_4_1_2055 99 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 130 244 2 49 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 130 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 97 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 130 244 2 48 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 130 244 (accept_3_3 95 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 130 244 2 47 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 244 2 46 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 130 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 130 244 2 45 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 130 244 (accept_3_3 89 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 130 244 2 44 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 244 2 43 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 130 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 130 244 2 42 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 130 244 (accept_3_3 83 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 244 2 41 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 244 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 244 2 40 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 244 2 39 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 244 (accept_3_3 77 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 244 2 38 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 244 2 37 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 244 2 36 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 244 (accept_3_3 71 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 244 2 35 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 244 2 34 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 244 2 33 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 244 (accept_3_3 65 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 244 2 32 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 244 (Polychromatic418967fa.accept_17_12_11_6_1_3729 63 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 244 2 31 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 244 2 30 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 244 (accept_3_3 59 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 244 2 29 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 244 2 28 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 244
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 244 2 27 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 244 (accept_3_3 53 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 244 2 26 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 244 2 25 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 244 2 24 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 244 (accept_3_3 47 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 244 2 23 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 244 2 22 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 244 2 21 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 244 (accept_3_3 41 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 244 2 20 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 244 2 19 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 244
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 244 2 18 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 244 (accept_3_3 35 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 244 2 17 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 244 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 244 2 16 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 244
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 244 2 15 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 244 (accept_3_3 29 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 244 2 14 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 244 (Polychromatic418967fa.accept_21_6_4_13_1_8740 27 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 244 2 13 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 244 2 12 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 244 (accept_3_3 23 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 244 2 11 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 244 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 244 2 10 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 244
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 244 2 9 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 244 (accept_3_3 17 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 244 2 8 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 244 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 244 2 7 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 244
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 244 2 6 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 130 244 (accept_3_3 11 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 244 2 5 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 244 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 130 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 244 2 4 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 244
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 244 2 3 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 244 (accept_3_3 5 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  244 2 2 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 244 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 130 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 244 2 1 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 244 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 130 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 129 244 (Eq.refl Bool.true) (allA_succ_of_accept 115 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1
  115 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 114 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 129 244 (accept_3_3 113 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 129 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 112 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 129 244 (Polychromatic418967fa.accept_13_7_12_10_1_640 111 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 129 244 (accept_3_3 110 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 244
  (Polychromatic418967fa.accept_10_8_9_4_1_961 108 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 129 244 (accept_3_3 107 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 129 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 129 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 244 (accept_3_3 104 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 102 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 129 244 (accept_3_3 101 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 129 244 (Polychromatic418967fa.accept_13_8_12_10_1_4414 99 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 244 (accept_3_3 98 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 129 244 (accept_3_3 95 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 129 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 244 (accept_3_3 92 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 129 244 (accept_3_3 89 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 129 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 129 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 244 (accept_3_3 86 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 244
  (Polychromatic418967fa.accept_13_6_12_10_1_690 84 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 244 (accept_3_3 83 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 244 (Polychromatic418967fa.accept_11_5_8_2_1_588 82 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 244 (accept_3_3 80 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 244 (accept_3_3 77 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 244 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 244 (accept_3_3 74 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 244 (accept_3_3 71 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 129 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 244 (accept_3_3 68 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 244 (accept_3_3 65 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 244 (Polychromatic418967fa.accept_22_20_19_2_1_3572 64 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 244 (accept_3_3 62 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 244 (accept_3_3 59 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 244 (Polychromatic418967fa.accept_15_12_9_4_1_3898 57 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 244 (accept_3_3 56 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 244
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 244 (accept_3_3 53 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 244 (accept_3_3 50 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 244
  (Polychromatic418967fa.accept_10_8_9_4_1_961 48 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 244 (accept_3_3 47 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 244 (accept_3_3 44 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 244 (accept_3_3 41 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 244 (accept_3_3 38 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 244
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 244 (accept_3_3 35 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 244 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 244 (accept_3_3 32 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 244
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 244 (accept_3_3 29 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 244 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 244 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 244 (accept_3_3 26 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 244 (accept_3_3 23 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 244 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 244 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 244 (accept_3_3 20 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 244
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 244 (accept_3_3 17 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 244 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 244 (accept_3_3 14 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 244
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 244 (accept_3_3 11 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 244 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 244 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 244 (accept_3_3 8 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 244
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 244 (accept_3_3 5 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 244 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 244 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 244 (accept_3_3 2 129 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 244 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 128 244 (Eq.refl Bool.true) (allA_of_3_1 117 128 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 127 244 (Eq.refl Bool.true) (allA_succ_of_accept 117 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 244 (accept_3_3 116 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 115 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 114 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 244 (accept_3_3 113 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 112 127
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 244 (accept_3_3 110 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 244 (Polychromatic418967fa.accept_19_14_13_16_1_9318 109 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 244 (Polychromatic418967fa.accept_15_3_7_4_1_1225 108 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 244 (accept_3_3 107 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 244
  (Polychromatic418967fa.accept_12_10_7_4_1_820 106 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 127 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 105 127 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 127 244 (accept_3_3 104 127 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 103 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 127 244
  (Polychromatic418967fa.accept_10_2_7_4_1_967 102 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 127 244 (accept_3_3 101 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 127 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 244 (accept_3_3 98 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 244 (Polychromatic418967fa.accept_19_2_13_16_1_5089 97 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 244
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 244 (accept_3_3 95 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 244 (accept_3_3 92 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 244
  (Polychromatic418967fa.accept_19_14_13_16_1_9318 90 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 127 244 (accept_3_3 89 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 127 244 (Polychromatic418967fa.accept_16_8_15_4_1_5402 88 127 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 244 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 244 (accept_3_3 86 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 244
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 85 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 127 244 (Polychromatic418967fa.accept_24_12_7_4_1_13019 84 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 244 (accept_3_3 83 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 244 (accept_3_3 80 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 244 (Polychromatic418967fa.accept_15_3_7_4_1_1225 78 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 244 (accept_3_3 77 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 244 (Polychromatic418967fa.accept_16_12_15_4_1_5422 76 127
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 244 (accept_3_3 74 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 73 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 244 (accept_3_3 71 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 244 (accept_3_3 68 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 244 (Polychromatic418967fa.accept_17_15_8_6_1_8733 66 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 244 (accept_3_3 65 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 244 (Polychromatic418967fa.accept_25_14_2_19_1_7566 64 127
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 244 (accept_3_3 62 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 244 (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 244 (accept_3_3 59 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 244 (accept_3_3 56 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 244 (accept_3_3 53 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 244 (accept_3_3 50 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 244 (Polychromatic418967fa.accept_14_7_1_6_1_3514 49 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 244 (accept_3_3 47 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 244 (accept_3_3 44 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 244 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 244 (accept_3_3 41 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 244 (accept_3_3 38 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 244 (Polychromatic418967fa.accept_19_17_13_16_1_5118 36 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 244 (accept_3_3 35 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 127
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 244 (accept_3_3 32 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 244 (accept_3_3 29 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 244 (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 244 (accept_3_3 26 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 244 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 244 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 244 (accept_3_3 23 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 244 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 127
  244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 244 (accept_3_3 20 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 244 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 244 (accept_3_3 17 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 244 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 244 (accept_3_3 14 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 244 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 244 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 244 (accept_3_3 11 127 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 244 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 244 (accept_3_3 8 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 244 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 244 (Polychromatic418967fa.accept_22_6_17_2_1_3518 6 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 244 (accept_3_3 5 127 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 244 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 127 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 244
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 244 (accept_3_3 2 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 244 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 127 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  244))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 126 244 (Eq.refl Bool.true) (allA_succ_of_gcd 118 126 244 2 59 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 126 244
  (Polychromatic418967fa.accept_12_9_6_4_1_402 117 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 126 244 2 58 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 126 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 115 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 126 244 2 57 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 244 (accept_3_3 113 126 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 244 2 56 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 126 244
  (Polychromatic418967fa.accept_12_3_6_4_1_400 111 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 126 244 2 55 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 126 244 (Polychromatic418967fa.accept_19_14_12_16_1_7952 109 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 126 244 2 54 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 126 244 (accept_3_3 107 126 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 244 2 53 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 105 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 244 2 52 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 244 (Polychromatic418967fa.accept_13_12_9_10_1_1223 103 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 126 244 2 51 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 126 244 (accept_3_3 101 126 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 244 2 50 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 244
  (Polychromatic418967fa.accept_12_3_6_4_1_400 99 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 244 2 49 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 244 (Polychromatic418967fa.accept_13_6_9_10_1_1201 97 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 244 2 48 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 244 (accept_3_3 95 126 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 244 2 47 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 244
  (Polychromatic418967fa.accept_12_9_6_4_1_402 93 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 244 2 46 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 244 (Polychromatic418967fa.accept_19_15_12_16_1_3819 91 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 126 244 2 45 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 244 (accept_3_3 89 126 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 244 2 44 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 244
  (Polychromatic418967fa.accept_12_3_6_4_1_400 87 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 244 2 43 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 85 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 244 2 42 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 244 (accept_3_3 83 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 244 2 41 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402
  81 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 244 2 40 63 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 244
  (Polychromatic418967fa.accept_13_1_9_10_1_625 79 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 244 2 39 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 244 (accept_3_3 77 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 244 2 38 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 75 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 244 2 37 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 244
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 73 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 244 2 36 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 244 (accept_3_3 71 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 244 2 35 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 244 2 34 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 244
  (Polychromatic418967fa.accept_17_16_7_6_1_7343 67 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 244 2 33 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 244 (accept_3_3 65 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 244 2 32 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 244 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 244 2 31 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 244
  (Polychromatic418967fa.accept_19_4_12_16_1_2574 61 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 244 2 30 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 244 (accept_3_3 59 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 244 2 29 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 244 2 28 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 244 2 27 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 244 (accept_3_3 53 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 244 2 26 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 244 2 25 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 244
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 49 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 244 2 24 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 244 (accept_3_3 47 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 244 2 23 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 244 2 22 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 244
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 244 2 21 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 244 (accept_3_3 41 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 244 2 20 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 244 2 19 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 244
  (Polychromatic418967fa.accept_25_12_1_19_1_7695 37 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 244 2 18 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 244 (accept_3_3 35 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 244 2 17 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 244 2 16 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 244
  (Polychromatic418967fa.accept_16_15_14_4_1_6649 31 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 244 2 15 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 244 (accept_3_3 29 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 244 2 14 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 244 2 13 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 244
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 244 2 12 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 244 (accept_3_3 23 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 244 2 11 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 244 2 10 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 244
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 244 2 9 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 244 (accept_3_3 17 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 244 2 8 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 244 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 244 2 7 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 244
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 244 2 6 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 244 (accept_3_3 11 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 244 2 5 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 244 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 244 2 4 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 244
  (Polychromatic418967fa.accept_16_7_14_4_1_1362 7 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 244 2 3 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 244 (accept_3_3 5 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  244 2 2 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 244 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 244 2 1 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 244 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 126 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 125 244 (Eq.refl Bool.true) (allA_of_3_1 120 125 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 121 124 244 (Eq.refl Bool.true) (allA_succ_of_gcd 120 124 244 4 30 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 124 244 (accept_3_3 119 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 124 244 2 59 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 124 244
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 117 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 124 244 4 29 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 124 244 (Polychromatic418967fa.accept_16_3_12_4_1_170 115 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 124 244 2 57 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 124 244 (accept_3_3
  113 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 124 244 4 28 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 124 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 111 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 124 244 2 55 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 124 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 124 244 4 27 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 124 244 (accept_3_3 107 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 124 244 2 53 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 124 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 105 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 124 244 4 26 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 124 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 124 244 2 51 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 124 244 (accept_3_3 101 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 124 244 4 25 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 124 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 124 244 2 49 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 124 244 (Polychromatic418967fa.accept_14_13_12_6_1_2735 97 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 124 244 4 24 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 124 244 (accept_3_3 95 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 124 244 2 47 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 124 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 93 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 124 244 4 23 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 124 244 (Polychromatic418967fa.accept_16_11_12_4_1_3195 91 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 124 244 2 45 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 124 244 (accept_3_3 89 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 124 244 4 22 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 124 244
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 124 244 2 43 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 124 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 124 244 4 21 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 124 244 (accept_3_3 83 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 124 244 2 41 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 124 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 81
  124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 244 4 20 31 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 244
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 79 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 124 244 2 39 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 124 244 (accept_3_3 77 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 244 4 19 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 244 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 244 2 37 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 244
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 244 4 18 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 244 (accept_3_3 71 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 244 2 35 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 244 4 17 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 244
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 244 2 33 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 244 (accept_3_3 65 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 244 4 16 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 244 (Polychromatic418967fa.accept_16_15_12_4_1_4324 63 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 244 2 31 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 244
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 61 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 124 244 4 15 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 124 244 (accept_3_3 59 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 244 2 29 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 244 4 14 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 244
  (Polychromatic418967fa.accept_13_3_7_10_1_668 55 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 244 2 27 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 244 (accept_3_3 53 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 244 4 13 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 244 2 25 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 244 4 12 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 244 (accept_3_3 47 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 244 2 23 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 244 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 244 4 11 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 244
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 244 2 21 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 244 (accept_3_3 41 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 244 4 10 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 244 2 19 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 244
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 37 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 244 4 9 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 244 (accept_3_3 35 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 244 2 17 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 244 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 124 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 244 4 8 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 244 (Polychromatic418967fa.accept_9_4_7_1_1_379 31
  124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 244 2 15 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 244 (accept_3_3 29
  124 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 244 4 7 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 244
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 124 244 2 13 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 124 244 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 244 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 244 4 6 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 244 (accept_3_3 23 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 244 2 11 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 244 4 5 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 244 (Polychromatic418967fa.accept_16_3_12_4_1_170 19 124 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 244 2 9 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 244 (accept_3_3 17 124 244 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 244 4 4 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 244 2 7 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 244
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 244 4 3 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 244 (accept_3_3 11 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 244 2 5 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 244 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 124 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 244 4 2 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 244 (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 124 244
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 244 2 3 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 244 (accept_3_3 5
  124 244 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 244 4 1 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 244
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 124 244 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 124 244 2 1 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 124 244 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 244 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 124
  244)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_244_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


