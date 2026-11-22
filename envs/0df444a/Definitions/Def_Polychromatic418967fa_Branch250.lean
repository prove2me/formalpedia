-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch250
-- name    : Polychromatic418967fa_Branch250
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:11.279255+00:00
-- url     : https://prove2.me/theorems/35d72c5d-52b0-4b4a-a336-0ac19b4c09db
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch250_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_250 : allB 250 250 :=
  allB_succ' 2 249 250 (Eq.refl Bool.true) (allA_succ_of_accept 1 249 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  249 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 250)) (allB_succ' 3 248 250
  (Eq.refl Bool.true) (allA_of_3_1 3 248 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 247 250 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 247 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 247 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 250 (accept_3_3 2 247 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 247 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 250)))) (allB_succ' 5 246 250 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 246 250 2 2 123 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 246 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 246 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 246 250 2 1 123 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 250
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 246 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 250))))) (allB_succ' 6 245 250 (Eq.refl Bool.true) (allA_of_3_1 6 245 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 7 244 250 (Eq.refl Bool.true) (allA_succ_of_gcd 6 244 250 2 3 122 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 250 (accept_3_3 5 244 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 250 2 2 122 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 244 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 244 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 244 250 2 1 122 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 244 250 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 244 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 250))))))) (allB_succ' 8 243 250 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 243 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 243 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 243 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 250 (accept_3_3 5 243 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 250 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  4 243 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 250
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 3 243 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 250 (accept_3_3 2 243 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 243 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 250)))))))) (allB_succ' 9 242 250 (Eq.refl Bool.true) (allA_of_3_1 9 242 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 241 250 (Eq.refl Bool.true) (allA_succ_of_accept 9 241 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 241 250 (accept_3_3 8 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  241 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 241 250 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 241 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 250 (accept_3_3 5 241 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 241 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 250 (accept_3_3 2 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 241 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 250)))))))))) (allB_succ' 11 240 250 (Eq.refl Bool.true) (allA_succ_of_gcd 10 240 250 10 1
  24 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 250
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 240 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 240 250 2 4 120 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 240 250 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 240 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 250 2 3 120 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 240 250 5 1 48 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 240 250 2 2 120 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 240 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 250 2 1 120 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 240 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 250))))))))))) (allB_succ' 12 239 250 (Eq.refl Bool.true)
  (allA_of_3_1 12 239 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 238 250 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 238 250 2 6 119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 238 250 (accept_3_3 11 238 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 238 250 2 5 119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 238 250 (Polychromatic418967fa.accept_19_9_10_3_1_1738 9 238 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 238 250 2 4 119 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 238 250
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 238 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 238 250 2 3 119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 238 250 (accept_3_3 5 238 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 250 2 2 119 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 238 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 250 2 1 119 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 238 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 250))))))))))))) (allB_succ' 14 237 250 (Eq.refl Bool.true) (allA_succ_of_accept 13 237 250
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 237 250 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 237 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 250 (accept_3_3 11 237 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 237 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 250
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 237 250 (accept_3_3 8 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  237 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 237 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 250 (accept_3_3 5 237 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 237 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 250 (accept_3_3 2 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 237 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 250)))))))))))))) (allB_succ' 15 236 250 (Eq.refl Bool.true) (allA_of_3_1 15 236 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 235 250 (Eq.refl Bool.true) (allA_succ_of_gcd 15 235 250 5 3
  47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 235 250
  (accept_3_3 14 235 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 235 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 235 250 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 235 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 250 (accept_3_3 11 235 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 235 250 5 2 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 235 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 235 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 250 (accept_3_3 8 235 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 250 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 235 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 250
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 235 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 235 250 5 1 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 235 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 250 (accept_3_3 2 235 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  235 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 250)))))))))))))))) (allB_succ' 17
  234 250 (Eq.refl Bool.true) (allA_succ_of_gcd 16 234 250 2 8 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 234 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 234 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 250 2 7 117 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 250
  (Polychromatic418967fa.accept_23_13_4_20_1_15113 13 234 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 234 250 2 6 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 234 250 (accept_3_3 11 234 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 250 2 5 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 250 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 234 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 250 2 4 117 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 250
  (Polychromatic418967fa.accept_19_7_6_3_1_6998 7 234 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 250 2 3 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 250 (accept_3_3 5 234 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 250 2 2 117 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 234 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 250 2 1 117 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 250
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 234 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 250))))))))))))))))) (allB_succ' 18 233 250 (Eq.refl Bool.true) (allA_of_3_1 18 233 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 232 250 (Eq.refl Bool.true) (allA_succ_of_gcd 18 232 250 2 9 116 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 232 250
  (accept_3_3 17 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 232 250 2 8 116 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 232 250
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 232 250 2 7 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 232 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 232 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 232 250 2 6 116 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 232 250 (accept_3_3 11 232 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 232 250 2 5 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 232 250 (Polychromatic418967fa.accept_27_9_16_7_1_9526
  9 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 250 2 4 116 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 250
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 250 2 3 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 250 (accept_3_3 5 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 250 2 2 116 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 250 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 232 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 250 2 1 116 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 250
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 232 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 250))))))))))))))))))) (allB_succ' 20 231 250 (Eq.refl Bool.true) (allA_succ_of_accept 19 231 250
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 231 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 231 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 250 (accept_3_3 17 231 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 231 250 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 231 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 250
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 231 250 (accept_3_3 14 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 231 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 231 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 231 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 250 (accept_3_3 11 231 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 250 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 231 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 250
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 231 250 (accept_3_3 8 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  231 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 231 250 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 231 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 250 (accept_3_3 5 231 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 250 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 231 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 250
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 250 (accept_3_3 2 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 250)))))))))))))))))))) (allB_succ' 21 230 250 (Eq.refl Bool.true) (allA_of_3_1 21 230 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 229 250 (Eq.refl Bool.true) (allA_succ_of_accept 21 229 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 250 (accept_3_3 20 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 250 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 229 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 250 (accept_3_3 17 229 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 229
  250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 250 (accept_3_3 14 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 250 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 229 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 250 (accept_3_3 11 229 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 229 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 250
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 250 (accept_3_3 8 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 250 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 229 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 250 (accept_3_3 5 229 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 229 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 250 (accept_3_3 2 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 250 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 229 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 250)))))))))))))))))))))) (allB_succ' 23 228 250 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  228 250 2 11 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 228 250 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 228 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 250 2 10 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 19
  228 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 250 2 9 114 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 250 (accept_3_3 17
  228 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 250 2 8 114 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 228 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 228 250 2 7 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 228 250 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 228 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 250 2 6 114 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 250 (accept_3_3 11 228 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 250 2 5 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 250 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  228 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 250 2 4 114 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 250
  (Polychromatic418967fa.accept_15_7_3_10_1_817 7 228 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 250 2 3 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 228 250 (accept_3_3 5 228 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 228 250 2 2 114 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 228 250 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 228 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 250 2 1 114 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 250
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 228 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 250))))))))))))))))))))))) (allB_succ' 24 227 250 (Eq.refl Bool.true) (allA_of_3_1 24 227 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 226 250 (Eq.refl Bool.true) (allA_succ_of_gcd 24 226 250 2 12 113 125
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 226 250
  (accept_3_3 23 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 226 250 2 11 113 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 226 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 226 250 2 10 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 226 250 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 226 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 226 250 2 9 113 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 226 250 (accept_3_3 17 226 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 226 250 2 8 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 226 250 (Polychromatic418967fa.accept_9_6_1_7_1_577 15
  226 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 250 2 7 113 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 250
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 250 2 6 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 250 (accept_3_3 11 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 250 2 5 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 250 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 226 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 250 2 4 113 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 250
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 250 2 3 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 250 (accept_3_3 5 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 250 2 2 113 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 226 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 250 2 1 113 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 250
  (Polychromatic418967fa.accept_13_1_5_3_1_888 1 226 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 250))))))))))))))))))))))))) (allB_succ' 26 225 250 (Eq.refl Bool.true) (allA_succ_of_gcd 25 225 250 25
  1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 225 250
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 225 250 (accept_3_3 23 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 225 250 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 225 250 (Polychromatic418967fa.accept_19_2_16_3_1_7005 21 225 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 225 250 5 4 45 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 225 250
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 225 250 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 225 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 250 (accept_3_3 17 225 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 225 250 (Polychromatic418967fa.accept_20_16_5_10_1_6487 16 225 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 250 5 3 45 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 250 (accept_3_3 14 225 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 250
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 250 (accept_3_3 11 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  225 250 5 2 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 225 250 (Polychromatic418967fa.accept_16_9_1_10_1_3610 9 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 250 (accept_3_3 8 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 250 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 225 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 225 250 5 1 45 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 250
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 225 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 225 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 250 (accept_3_3 2 225 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 225 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 250)))))))))))))))))))))))))) (allB_succ' 27 224 250 (Eq.refl
  Bool.true) (allA_of_3_1 27 224 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 223 250 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 223 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 223 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 250 (accept_3_3 26 223 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 223 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 250 (Polychromatic418967fa.accept_13_11_2_3_1_883
  24 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 250 (accept_3_3 23
  223 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 250
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 223 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 223 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 250 (accept_3_3 20 223 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 223 250 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 223 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 250
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 250 (accept_3_3 17 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 250 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 250 (accept_3_3 14 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 223 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 250
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 250 (accept_3_3 11 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 250 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 250 (accept_3_3 8 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 250 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 223 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 250
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 250 (accept_3_3 5 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 250 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 223 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 250 (accept_3_3 2 223 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 250)))))))))))))))))))))))))))) (allB_succ' 29 222
  250 (Eq.refl Bool.true) (allA_succ_of_gcd 28 222 250 2 14 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 222 250 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 222 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 250 2 13 111 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 250
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 25 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 250 2 12 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 250 (accept_3_3 23 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 250 2 11 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 222 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 222 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 250 2 10 111 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 250 2 9 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 250 (accept_3_3 17 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 250 2 8 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 250 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 222 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 250 2 7 111 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 250
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 250 2 6 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 250 (accept_3_3 11 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 250 2 5 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 250 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 222 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 250 2 4 111 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 250
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 250 2 3 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 250 (accept_3_3 5 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 250 2 2 111 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 250 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 222 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 250 2 1 111 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 250
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 222 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 250))))))))))))))))))))))))))))) (allB_succ' 30 221 250 (Eq.refl Bool.true) (allA_of_3_1 30 221 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 220 250 (Eq.refl Bool.true) (allA_succ_of_gcd 30 220 250 10 3
  22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 250
  (accept_3_3 29 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 250 2 14 110 125 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 250
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 220 250 2 13 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 220 250 5 5 44 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 220 250 2 12 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 250 (accept_3_3 23 220 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 220 250 2 11 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 220 250 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 220 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 250 10 2 22 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 250
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 250 2 9 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 250 (accept_3_3 17 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 250 2 8 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 220 250 5 3 44 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 220 250 2 7 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 220 250 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 220 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 220 250 2 6 110 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 220 250 (accept_3_3 11 220 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 250 10 1 22 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 250
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 220 250 2 4 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 220 250 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 220 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 250 2 3 110 125 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 220 250 5 1 44 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 220 250 2 2 110 125 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 250
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 220 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 250 2 1 110 125 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 250 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 220 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 250))))))))))))))))))))))))))))))) (allB_succ' 32 219 250
  (Eq.refl Bool.true) (allA_succ_of_accept 31 219 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 250
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 250 (accept_3_3 29 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 250 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 250 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 250 (accept_3_3 26 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 219 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 250
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 250 (accept_3_3 23 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 250 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 250 (accept_3_3 20 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 250
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 250 (accept_3_3 17 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 250 (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 219 250 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 250 (accept_3_3 14 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 250
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 250 (accept_3_3 11 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 219 250 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 250 (accept_3_3 8 219 250
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 250 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 250
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 219 250 (accept_3_3 5 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  219 250 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 219 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 219 250 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 250 (accept_3_3 2 219 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 250 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 250)))))))))))))))))))))))))))))))) (allB_succ' 33
  218 250 (Eq.refl Bool.true) (allA_of_3_1 33 218 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 217 250
  (Eq.refl Bool.true) (allA_succ_of_accept 33 217 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 250 (accept_3_3 32 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 217 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 250 (accept_3_3 29 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 250 (accept_3_3 26 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 250 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 217 250
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 250 (accept_3_3 23 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 250 (accept_3_3 20 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 250
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 250 (accept_3_3 17 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 250 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 250 (accept_3_3 14 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 250
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 250 (accept_3_3 11 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 250 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 250 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 250 (accept_3_3 8 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 250
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 250 (accept_3_3 5 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 250 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 250 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 250 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 250 (accept_3_3 2 217 250 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 250 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 217 250 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 250))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_250_segment_001)))))))))))))))))))))))))))))))))


