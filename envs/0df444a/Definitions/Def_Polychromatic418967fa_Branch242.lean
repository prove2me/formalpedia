-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch242
-- name    : Polychromatic418967fa_Branch242
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:24.694186+00:00
-- url     : https://prove2.me/theorems/a52eb8bd-2943-4b30-95a4-8095579f6df8
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch242_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_242 : allB 242 242 :=
  allB_succ' 2 241 242 (Eq.refl Bool.true) (allA_of_3_0 2 241 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  240 242 (Eq.refl Bool.true) (allA_succ_of_gcd 2 240 242 2 1 120 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 242 (accept_3_2 1 240 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 240 242))) (allB_succ' 4 239 242 (Eq.refl Bool.true) (allA_succ_of_accept 3 239 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 239 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 239 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 242 (accept_3_2 1 239 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 239 242)))) (allB_succ' 5 238 242 (Eq.refl Bool.true) (allA_of_3_0 5 238 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 237 242 (Eq.refl Bool.true) (allA_succ_of_accept 5 237 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 242 (accept_3_2 4 237 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 237 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 237 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 242 (accept_3_2 1 237 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 242)))))) (allB_succ' 7 236 242 (Eq.refl Bool.true) (allA_succ_of_gcd 6 236 242 2 3
  118 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 236 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 236 242 2 2 118 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 236 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 236 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 236 242 2 1 118 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 236 242 (accept_3_2 1 236 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 236 242))))))) (allB_succ' 8 235 242 (Eq.refl Bool.true) (allA_of_3_0 8 235
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 234 242 (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 242 2 4
  117 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 242
  (accept_3_2 7 234 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 242 2 3 117 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 242
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 5 234 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 242 2 2 117 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 234 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 242 2 1 117 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 242 (accept_3_2 1 234 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 242))))))))) (allB_succ' 10 233 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 233 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 233 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 242 (accept_3_2 7 233 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  233 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 233 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 242 (accept_3_2 4 233 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 233 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 242 (accept_3_2 1 233 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 242)))))))))) (allB_succ' 11 232 242 (Eq.refl Bool.true) (allA_of_3_0 11 232 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 231 242 (Eq.refl Bool.true) (allA_succ_of_gcd 11 231 242 11 1
  21 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 231 242
  (accept_3_2 10 231 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 231 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 231 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 231 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 242 (accept_3_2 7 231 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 231 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 231 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  231 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 242 (accept_3_2 4 231
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 231 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 231 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 242 (accept_3_2 1 231 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 242)))))))))))) (allB_succ' 13 230 242 (Eq.refl Bool.true) (allA_succ_of_gcd 12 230 242 2 6
  115 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 230
  242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 230 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 242 2 5 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 230 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 230 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 242 2 4 115 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 242 (accept_3_2 7 230 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 242 2 3 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 230 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5
  230 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 242 2 2 115 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 230 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 242 2 1 115 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 242 (accept_3_2 1 230 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  242))))))))))))) (allB_succ' 14 229 242 (Eq.refl Bool.true) (allA_of_3_0 14 229 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 228 242 (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 242 2 7 114 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 242 (accept_3_2 13 228 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 242 2 6 114 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 228 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 228 242 2 5 114 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 228 242 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 228 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 242 2 4 114 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 242 (accept_3_2 7 228 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 242 2 3 114 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 5
  228 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 242 2 2 114 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 242
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 228 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 242 2 1 114 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 242 (accept_3_2 1 228 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  242))))))))))))))) (allB_succ' 16 227 242 (Eq.refl Bool.true) (allA_succ_of_accept 15 227 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 227 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 227 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 242 (accept_3_2 13 227 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 227 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 227 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 242
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 242 (accept_3_2 10 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 227 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 242 (accept_3_2 7 227 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 227 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 242 (accept_3_2 4 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 242 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 227 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 242 (accept_3_2 1 227 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 242)))))))))))))))) (allB_succ' 17 226 242 (Eq.refl Bool.true) (allA_of_3_0 17 226
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 225 242 (Eq.refl Bool.true) (allA_succ_of_accept 17 225
  242 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 225 242 (accept_3_2 16 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 225 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 225 242 (Polychromatic418967fa.accept_26_14_17_8_1_14599 14 225 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 242 (accept_3_2 13 225 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 225 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 242 (accept_3_2 10 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  225 242 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 225 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 242 (accept_3_2 7 225 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 225 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 242 (accept_3_2 4 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 242 (Polychromatic418967fa.accept_19_2_16_14_1_3551 2 225 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 242 (accept_3_2 1 225 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 242)))))))))))))))))) (allB_succ' 19 224 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 224 242 2 9 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 224 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 224 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 242 2 8 112 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 242
  (Polychromatic418967fa.accept_20_15_4_2_1_5914 15 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 242 2 7 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 242 (accept_3_2 13 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 242 2 6 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 224 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 224 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 242 2 5 112 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 242
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 242 2 4 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 242 (accept_3_2 7 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 242 2 3 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 224 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 242 2 2 112 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 242
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 3 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 242 2 1 112 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 242 (accept_3_2 1 224 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  242))))))))))))))))))) (allB_succ' 20 223 242 (Eq.refl Bool.true) (allA_of_3_0 20 223 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 222 242 (Eq.refl Bool.true) (allA_succ_of_gcd 20 222 242 2 10 111 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 242 (accept_3_2 19 222 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 222 242 2 9 111 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 222 242
  (Polychromatic418967fa.accept_26_17_14_8_1_9114 17 222 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 222 242 2 8 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 222 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 222 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 242 2 7 111 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 242 (accept_3_2 13 222 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 242 2 6 111 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 222 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 242 2 5 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 222 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 242 2 4 111 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 242 (accept_3_2 7 222 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 242 2 3 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  222 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 242 2 2 111 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 222 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 242 2 1 111 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 242 (accept_3_2 1 222 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  242))))))))))))))))))))) (allB_succ' 22 221 242 (Eq.refl Bool.true) (allA_succ_of_accept 21 221 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 221 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 221 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 242 (accept_3_2 19 221 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 221 242 (Polychromatic418967fa.accept_26_18_13_8_1_14598 18 221 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 242
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 242 (accept_3_2 16 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 242 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 221 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 242 (accept_3_2 13 221 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 221 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 242 (accept_3_2 10 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 221 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 242 (accept_3_2 7 221 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 221 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 242
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 242 (accept_3_2 4 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 221 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 242 (accept_3_2 1 221 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 242)))))))))))))))))))))) (allB_succ' 23 220 242 (Eq.refl Bool.true) (allA_of_3_0
  23 220 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 219 242 (Eq.refl Bool.true) (allA_succ_of_accept 23
  219 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 219 242 (accept_3_2 22 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 219 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 219 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 219 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 242 (accept_3_2 19 219 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 242 (Polychromatic418967fa.accept_12_6_3_2_1_743
  18 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 242 (accept_3_2 16 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 242 (accept_3_2 13 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 242 (accept_3_2 10 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 242 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 242 (accept_3_2 7 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 219 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 242 (accept_3_2 4 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 242 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 219 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 242 (accept_3_2 1 219 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 242)))))))))))))))))))))))) (allB_succ' 25 218 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 218 242 2 12 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 218 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 242 2 11 109 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 242 2 10 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 242 (accept_3_2 19 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 242 2 9 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 218 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 242 2 8 109 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 242 2 7 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 242 (accept_3_2 13 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 242 2 6 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 242 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 218 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 242 2 5 109 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 242
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 242 2 4 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 242 (accept_3_2 7 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 242 2 3 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 218 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 242 2 2 109 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 242 2 1 109 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 242 (accept_3_2 1 218 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  242))))))))))))))))))))))))) (allB_succ' 26 217 242 (Eq.refl Bool.true) (allA_of_3_0 26 217 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 216 242 (Eq.refl Bool.true) (allA_succ_of_gcd 26 216 242 2 13 108 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 242 (accept_3_2 25
  216 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 242 2 12 108 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 216 242 2 11 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 216 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 216 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 242 2 10 108 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 242 (accept_3_2 19 216 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 242 2 9 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  216 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 242 2 8 108 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 242
  (Polychromatic418967fa.accept_19_15_7_14_1_11879 15 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 216 242 2 7 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 216 242 (accept_3_2 13 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 242 2 6 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 216 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 216 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 242 2 5 108 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 242 2 4 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 216 242 (accept_3_2 7 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 242 2 3 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 216 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 242 2 2 108 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 242 2 1 108 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 242 (accept_3_2 1 216 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  242))))))))))))))))))))))))))) (allB_succ' 28 215 242 (Eq.refl Bool.true) (allA_succ_of_accept 27 215 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 215 242 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 215 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 242 (accept_3_2 25 215 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 215 242 (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 215 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 242 (accept_3_2 22 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 242 (accept_3_2 19 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 215 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 242 (accept_3_2 16 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 242 (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 215 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 242 (accept_3_2 13 215 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 242 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 215
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 242
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 242 (accept_3_2 10 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 242 (accept_3_2 7 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 215 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 242 (accept_3_2 4 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 242 (accept_3_2 1 215 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 242)))))))))))))))))))))))))))) (allB_succ' 29 214 242 (Eq.refl Bool.true)
  (allA_of_3_0 29 214 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 213 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 213 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 242 (accept_3_2 28 213 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 213 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 242
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 26 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 242 (accept_3_2 25 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 213 242 (Polychromatic418967fa.accept_25_24_13_17_1_7336 24 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 213 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 242 (accept_3_2 22 213 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 242 (accept_3_2 19 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 242 (accept_3_2 16 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 213 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 242 (accept_3_2 13 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 242 (accept_3_2 10 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 242 (Polychromatic418967fa.accept_19_9_4_14_1_3642 9 213 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 242 (accept_3_2 7 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 242 (accept_3_2 4 213 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 242 (accept_3_2 1 213 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  242)))))))))))))))))))))))))))))) (allB_succ' 31 212 242 (Eq.refl Bool.true) (allA_succ_of_gcd 30 212 242 2 15 106 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 212 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 212 242 2 14 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 212 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 212 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 212 242 2 13 106 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 212 242 (accept_3_2 25 212 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 212 242 2 12 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  23 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 242 2 11 106 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 242 2 10 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 212 242 (accept_3_2 19 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 242 2 9 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 212 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 242 2 8 106 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 242 2 7 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 242 (accept_3_2 13 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 242 2 6 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 212 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 242 2 5 106 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 242
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 242 2 4 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 242 (accept_3_2 7 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 242 2 3 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 212 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 242 2 2 106 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 242 2 1 106 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 242 (accept_3_2 1 212 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  242))))))))))))))))))))))))))))))) (allB_succ' 32 211 242 (Eq.refl Bool.true) (allA_of_3_0 32 211 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 210 242 (Eq.refl Bool.true) (allA_succ_of_gcd 32 210 242 2 16 105 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 242
  (accept_3_2 31 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 210 242 2 15 105 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 210 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 242 2 14 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 210 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 210 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 242 2 13 105 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 242 (accept_3_2 25 210 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 210 242 2 12 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 242 2 11 105 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 242 2 10 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 242 (accept_3_2 19 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 242 2 9 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 242 (Polychromatic418967fa.accept_19_17_1_14_1_6360 17 210 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 242 2 8 105 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 242 2 7 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 242 (accept_3_2 13 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 242 2 6 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 242 2 5 105 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 242 2 4 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 242 (accept_3_2 7 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 242 2 3 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 210 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 242 2 2 105 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 242 2 1 105 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 242 (accept_3_2 1 210 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  242))))))))))))))))))))))))))))))))) (allB_succ' 34 209 242 (Eq.refl Bool.true) (allA_succ_of_gcd 33 209 242 11 3 19
  22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 209 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 209 242 (accept_3_2 31 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 209 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 209 242 (Polychromatic418967fa.accept_21_8_20_11_1_7025 29 209 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 242 (accept_3_2 28 209 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 209 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 242 (accept_3_2 25 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 209 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 209 242 11 2 19 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 209 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 209 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 209 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 242 (accept_3_2 19 209 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 209 242 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 209 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 242 (accept_3_2 16 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 242 (accept_3_2 13 209 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 209 242 11 1 19 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 209 242 (accept_3_2 10 209 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 242 (accept_3_2 7 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 242 (accept_3_2 4 209 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 242 (accept_3_2 1 209 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  242)))))))))))))))))))))))))))))))))) (allB_succ' 35 208 242 (Eq.refl Bool.true) (allA_of_3_0 35 208 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 207 242 (Eq.refl Bool.true) (allA_succ_of_accept 35 207 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 242 (accept_3_2 34 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 242 (Polychromatic418967fa.accept_20_12_7_2_1_4448 32 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 242 (accept_3_2 31 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 207
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 242 (accept_3_2 28 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 242 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 242 (Polychromatic418967fa.accept_21_5_18_11_1_7041 26 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 242 (accept_3_2 25 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 207
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 242 (accept_3_2 22 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 242 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 242 (accept_3_2 19 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 207
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 242 (accept_3_2 16 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 242 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 242 (accept_3_2 13 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 242 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 207
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 242 (accept_3_2 10 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 242 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 242 (accept_3_2 7 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 207 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 242 (accept_3_2 4 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 242 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 207 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 242 (Polychromatic418967fa.accept_19_2_17_14_1_6399 2 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 242 (accept_3_2 1 207 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 242)))))))))))))))))))))))))))))))))))) (allB_succ' 37 206 242 (Eq.refl
  Bool.true) (allA_succ_of_gcd 36 206 242 2 18 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 206 242 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 206 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 242 2 17 103 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 242
  (Polychromatic418967fa.accept_23_10_22_12_1_14597 33 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 206 242 2 16 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 206 242 (accept_3_2 31 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 242 2 15 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 206 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 242 2 14 103 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 242 2 13 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 242 (accept_3_2 25 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 242 2 12 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 242 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 206 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 242 2 11 103 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 242 2 10 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 242 (accept_3_2 19 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 242 2 9 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 242 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 206 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 242 2 8 103 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 242 2 7 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 242 (accept_3_2 13 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 242 2 6 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 206 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 242 2 5 103 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 242
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 242 2 4 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 242 (accept_3_2 7 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 242 2 3 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 242 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 206 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 242 2 2 103 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 242
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 242 2 1 103 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 242 (accept_3_2 1 206 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  242))))))))))))))))))))))))))))))))))))) (allB_succ' 38 205 242 (Eq.refl Bool.true) (allA_of_3_0 38 205 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 204 242 (Eq.refl Bool.true) (allA_succ_of_gcd 38 204 242 2 19 102 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 242
  (accept_3_2 37 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 242 2 18 102 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 242
  (Polychromatic418967fa.accept_20_15_4_2_1_5914 35 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 204 242 2 17 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 204 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 204 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 242 2 16 102 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 242 (accept_3_2 31 204 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 242 2 15 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 242 2 14 102 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 204 242 2 13 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 242 (accept_3_2 25 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 242 2 12 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 204 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 204 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 242 2 11 102 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 242 2 10 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 204 242 (accept_3_2 19 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 242 2 9 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 204 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 204 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 242 2 8 102 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 242
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 15 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 204 242 2 7 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 204 242 (accept_3_2 13 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 242 2 6 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 204 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 242 2 5 102 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 242
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 204 242 2 4 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 204 242 (accept_3_2 7 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 242 2 3 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 242 2 2 102 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 242 2 1 102 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 242 (accept_3_2 1 204 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  242))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 203 242 (Eq.refl Bool.true) (allA_succ_of_accept 39 203 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 203 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 203 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 242 (accept_3_2 37 203 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 203 242 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 242
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 242 (accept_3_2 34 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 242 (accept_3_2 31 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 203 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 242 (accept_3_2 28 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 242 (Polychromatic418967fa.accept_21_5_14_11_1_10102 26 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 242 (accept_3_2 25 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 242
  (Polychromatic418967fa.accept_16_7_11_2_1_3117 23 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 242 (accept_3_2 22 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 242 (accept_3_2 19 203 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 242 (Polychromatic418967fa.accept_19_18_13_14_1_4995 18 203 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 242 (accept_3_2 16 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 242 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 242 (accept_3_2 13 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 242 (accept_3_2 10 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 242 (accept_3_2 7 203 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 242 (accept_3_2 4 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 242 (accept_3_2 1 203 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 242)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 202 242 (Eq.refl
  Bool.true) (allA_of_3_0 41 202 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 201 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 201 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 242 (accept_3_2 40 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 242 (Polychromatic418967fa.accept_9_2_3_8_1_318
  38 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 242 (accept_3_2 37
  201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 242 (accept_3_2 34 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 201 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 242 (Polychromatic418967fa.accept_9_5_3_8_1_316
  32 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 242 (accept_3_2 31
  201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 242 (accept_3_2 28 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 242 (Polychromatic418967fa.accept_10_6_1_2_1_874
  26 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 242 (accept_3_2 25
  201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 24 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 242 (accept_3_2 22 201 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 242 (Polychromatic418967fa.accept_24_21_9_2_1_14596 21 201 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 242 (accept_3_2 19 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 242 (accept_3_2 16 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 242 (accept_3_2 13 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 242 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 242 (accept_3_2 10 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 242 (accept_3_2 7 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 242 (accept_3_2 4 201 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 242 (accept_3_2 1 201 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  242)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 200 242 (Eq.refl Bool.true) (allA_succ_of_gcd 42 200 242
  2 21 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  200 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 200 242 2 20 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 200 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 200 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 242 2 19 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 242 (accept_3_2 37 200 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 242 2 18 100 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 200 242
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 200 242 2 17 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 200 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 242 2 16 100 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 242 (accept_3_2 31 200 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 242 2 15 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 242 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 242 2 14 100 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 242
  (Polychromatic418967fa.accept_13_1_5_8_1_207 27 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 242 2 13 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 200 242 (accept_3_2 25 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 242 2 12 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 200 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 242 2 11 100 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 242 2 10 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 242 (accept_3_2 19 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 242 2 9 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 200 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 242 2 8 100 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 242 2 7 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 242 (accept_3_2 13 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 242 2 6 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 200 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 242 2 5 100 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 242
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 242 2 4 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 242 (accept_3_2 7 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 242 2 3 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 242 2 2 100 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 242 2 1 100 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 242 (accept_3_2 1 200 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  242))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 199 242 (Eq.refl Bool.true) (allA_of_3_0 44 199 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 198 242 (Eq.refl Bool.true) (allA_succ_of_gcd 44 198 242 22 2
  9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 242
  (accept_3_2 43 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 198 242 2 21 99 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 198 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 198 242 2 20 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 198 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 198 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 198 242 2 19 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 242 (accept_3_2 37 198 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 198 242 2 18 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 198 242 (Polychromatic418967fa.accept_10_5_8_2_1_517
  35 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 242 2 17 99 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 242 11 3 18
  22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 242 2 16
  99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 242
  (accept_3_2 31 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 242 2 15 99 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 242
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 242 2 14 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 198 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 242 2 13 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 242 (accept_3_2 25 198 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 242 2 12 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 242 (Polychromatic418967fa.accept_14_9_2_4_1_1814
  23 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 242 22 1 9 11
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 242 2 10 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 242 (accept_3_2 19 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 242 2 9 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 242 (Polychromatic418967fa.accept_16_1_6_2_1_3100 17 198 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 242 2 8 99 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 242 2 7 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 242 (accept_3_2 13 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 242 2 6 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 198 242 11 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 198 242 2 5 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 242 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 198 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 242 2 4 99 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 242 (accept_3_2 7
  198 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 242 2 3 99 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 198 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 242 2 2 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 198 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 198 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 242 2 1 99 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 242 (accept_3_2 1 198 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198 242))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 197 242 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 197 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 242 (Polychromatic418967fa.accept_10_4_7_2_1_211
  44 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 242 (accept_3_2 43
  197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 242
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 42 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 197 242 (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 197 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 242 (accept_3_2 40 197 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 242 (Polychromatic418967fa.accept_7_3_1_4_1_121
  38 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 242 (accept_3_2 37
  197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 242
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 197 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 242 (accept_3_2 34 197 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 197 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 242 (Polychromatic418967fa.accept_12_8_5_2_1_746
  32 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 242 (accept_3_2 31
  197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 242
  (Polychromatic418967fa.accept_19_11_7_14_1_6394 30 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 242 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 242 (accept_3_2 28 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 242 (accept_3_2 25 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 242 (accept_3_2 22 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 242 (accept_3_2 19 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 242 (Polychromatic418967fa.accept_19_18_7_14_1_5012 18 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 242 (accept_3_2 16 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 242
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 242 (accept_3_2 13 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 242 (accept_3_2 10 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 242 (accept_3_2 7 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 242 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 242 (accept_3_2 4 197 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 242
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 242 (accept_3_2 1 197 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  242)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 196 242 (Eq.refl Bool.true) (allA_of_3_0 47 196 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 195 242 (Eq.refl Bool.true) (allA_succ_of_accept 47 195 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 242 (accept_3_2 46 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 195 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 195 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 242 (accept_3_2 43 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 242 (accept_3_2 40 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 242 (accept_3_2 37 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 242 (Polychromatic418967fa.accept_19_17_5_14_1_3587 36 195 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 242 (accept_3_2 34 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 242 (accept_3_2 31 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 242 (accept_3_2 28 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 242 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 242 (accept_3_2 25 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 242 (accept_3_2 22 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 242 (accept_3_2 19 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 242 (accept_3_2 16 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 242 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 242 (accept_3_2 13 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 242 (accept_3_2 10 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 242 (accept_3_2 7 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 195 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 242 (accept_3_2 4 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 242 (accept_3_2 1 195 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 242)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 194 242 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 194 242 2 24 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 194 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 194 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 242 2 23 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 242
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 242 2 22 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 242 (accept_3_2 43 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 242 2 21 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 194 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 242 2 20 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 242 2 19 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 242 (accept_3_2 37 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 242 2 18 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 242 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 194 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 242 2 17 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 242 2 16 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 242 (accept_3_2 31 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 242 2 15 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 194 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 242 2 14 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 242 2 13 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 242 (accept_3_2 25 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 242 2 12 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 194 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 242 2 11 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 242 2 10 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 242 (accept_3_2 19 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 242 2 9 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 194 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 242 2 8 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 242 2 7 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 242 (accept_3_2 13 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 242 2 6 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 242 2 5 97 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 242 2 4 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 242 (accept_3_2 7 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  242 2 3 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 242 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 194 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 242 2 2 97 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 194 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 242 2 1 97 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 242 (accept_3_2 1 194 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 242)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 193 242 (Eq.refl Bool.true) (allA_of_3_0 50 193 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 192 242 (Eq.refl Bool.true) (allA_succ_of_gcd 50 192 242 2 25 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 242 (accept_3_2 49 192 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 192 242 2 24 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 192 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 47
  192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 242 2 23 96 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 242
  (Polychromatic418967fa.accept_19_7_2_14_1_3569 45 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 192 242 2 22 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 192 242 (accept_3_2 43 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 242 2 21 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 192 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 242 2 20 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 242
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 242 2 19 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 242 (accept_3_2 37 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 242 2 18 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 242 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 192 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 242 2 17 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 242 2 16 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 192 242 (accept_3_2 31 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 242 2 15 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 242 2 14 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 242 2 13 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 242 (accept_3_2 25 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 242 2 12 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 192 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 242 2 11 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 242
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 242 2 10 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 192 242 (accept_3_2 19 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 242 2 9 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 242 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 192 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 242 2 8 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 242 2 7 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 242 (accept_3_2 13 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 242 2 6 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 242 2 5 96 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 242
  (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 242 2 4 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 242 (accept_3_2 7 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  242 2 3 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 242 2 2 96 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 242 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 192 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 242 2 1 96 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 242 (accept_3_2 1 192 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 242)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 191 242 (Eq.refl Bool.true) (allA_succ_of_accept 51 191 242 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 242 (accept_3_2 49 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 242 (accept_3_2 46 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 242 (accept_3_2 43 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 242 (accept_3_2 40 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 242
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 242 (accept_3_2 37 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 242 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 242 (accept_3_2 34 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 242 (accept_3_2 31 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 242 (accept_3_2 28 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 242 (accept_3_2 25 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 242 (accept_3_2 22 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 242 (accept_3_2 19 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 242 (Polychromatic418967fa.accept_19_18_1_14_1_4978 18 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 242 (accept_3_2 16 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 242 (accept_3_2 13 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 242 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 242 (accept_3_2 10 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 242 (accept_3_2 7 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 242 (accept_3_2 4 191 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 242
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 242 (accept_3_2 1 191 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  242)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 190 242 (Eq.refl Bool.true) (allA_of_3_0 53 190
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 189 242 (Eq.refl Bool.true) (allA_succ_of_accept 53 189
  242 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 189 242 (accept_3_2 52 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 189 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 242 (Polychromatic418967fa.accept_29_21_15_10_1_14573 50 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 242 (accept_3_2 49 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 242 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 242 (accept_3_2 46 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 242 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 242 (Polychromatic418967fa.accept_20_4_9_2_1_213 44 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 242 (accept_3_2 43 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 242 (accept_3_2 40 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 242 (Polychromatic418967fa.accept_13_12_7_8_1_1104 38 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 242 (accept_3_2 37 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 242 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 242 (accept_3_2 34 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 242 (Polychromatic418967fa.accept_20_13_9_2_1_5933 33 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 242 (Polychromatic418967fa.accept_17_15_2_4_1_2423 32 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 242 (accept_3_2 31 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 242 (accept_3_2 28 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 242 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 242 (accept_3_2 25 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 242 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 242 (accept_3_2 22 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 242 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 242 (Polychromatic418967fa.accept_19_1_18_14_1_6392 20 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 242 (accept_3_2 19 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 242 (accept_3_2 16 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 242 (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 242 (accept_3_2 13 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 242 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 189
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 242 (accept_3_2 10 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 242 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 242 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 189 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 242 (accept_3_2 7 189 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 242 (accept_3_2 4 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 242 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 189 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 242 (accept_3_2 1 189 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 242)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 188 242
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 188 242 2 27 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 188 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 188 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 242 2 26 94 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 242 2 25 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 242 (accept_3_2 49 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 242 2 24 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 242 2 23 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 188 242 2 22 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 188 242 (accept_3_2 43 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 242 2 21 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 242 2 20 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 242
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 242 2 19 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 242 (accept_3_2 37 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 242 2 18 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 242 2 17 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 242 2 16 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 188 242 (accept_3_2 31 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 242 2 15 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 242 2 14 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 242
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 242 2 13 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 242 (accept_3_2 25 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 242 2 12 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 242 2 11 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 242
  (Polychromatic418967fa.accept_15_6_8_2_1_104 21 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 242 2 10 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 242 (accept_3_2 19 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 242 2 9 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 188 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 242 2 8 94 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 242 2 7 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 242 (accept_3_2 13 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 242 2 6 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 188 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 242 2 5 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 242 2 4 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 242 (accept_3_2 7 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  242 2 3 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 188 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 242 2 2 94 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 188 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 242 2 1 94 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 242 (accept_3_2 1 188 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 242)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 187 242 (Eq.refl Bool.true) (allA_of_3_0 56 187 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 186 242 (Eq.refl Bool.true) (allA_succ_of_gcd 56 186 242 2 28 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 242 (accept_3_2 55 186 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 186 242 2 27 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 186 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128
  53 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 242 2 26 93 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 242 2 25 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 242 (accept_3_2 49 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 242 2 24 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 186 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 242 2 23 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 242 2 22 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 242 (accept_3_2 43 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 242 2 21 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 186 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 242 2 20 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 242 2 19 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 242 (accept_3_2 37 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 242 2 18 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 242 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 186 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 242 2 17 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 242 2 16 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 242 (accept_3_2 31 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 242 2 15 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 186 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 242 2 14 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 242 2 13 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 242 (accept_3_2 25 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 242 2 12 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 186 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 242 2 11 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 242 2 10 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 242 (accept_3_2 19 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 242 2 9 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 242 (Polychromatic418967fa.accept_19_17_15_14_1_3623 17 186 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 242 2 8 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 242 2 7 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 242 (accept_3_2 13 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 242 2 6 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 242 2 5 93 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 242 2 4 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 242 (accept_3_2 7 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  242 2 3 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 186 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 242 2 2 93 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 242 2 1 93 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 242 (accept_3_2 1 186 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 185 242 (Eq.refl Bool.true) (allA_succ_of_accept 57 185 242 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 185 242 (accept_3_2 55 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 185 242 (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 185 242 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 242 (accept_3_2 52 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 242 (accept_3_2 49 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 242 (accept_3_2 46 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 242 (accept_3_2 43 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 242 (accept_3_2 40 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 242 (accept_3_2 37 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 242 (accept_3_2 34 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 242 (accept_3_2 31 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 242 (accept_3_2 28 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 242
  (Polychromatic418967fa.accept_15_11_5_2_1_520 26 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 242 (accept_3_2 25 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 242 (accept_3_2 22 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 242 (accept_3_2 19 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 242 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 242 (accept_3_2 16 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 242
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 242 (accept_3_2 13 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 242 (accept_3_2 10 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 242 (accept_3_2 7 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 242 (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 242 (accept_3_2 4 185 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 242 (accept_3_2 1 185 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 184 242 (Eq.refl Bool.true) (allA_of_3_0
  59 184 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 183 242 (Eq.refl Bool.true) (allA_succ_of_accept 59
  183 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 183 242 (accept_3_2 58 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 183 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 183 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 183 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 242 (accept_3_2 55 183 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 242 (Polychromatic418967fa.accept_7_5_1_4_1_122
  54 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 183 242 (accept_3_2 52 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 183 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 183 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 242 (accept_3_2 49 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 242 (Polychromatic418967fa.accept_13_9_1_8_1_1742 48 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 242 (accept_3_2 46 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 183 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 183 242 (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 242 (accept_3_2 43 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 183 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 242 (accept_3_2 40 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 242 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 242 (accept_3_2 37 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 242 (Polychromatic418967fa.accept_19_17_12_14_1_3655 36 183 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 242 (accept_3_2 34 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 242 (accept_3_2 31 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 242 (accept_3_2 28 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 242 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 242 (accept_3_2 25 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 242 (accept_3_2 22 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 242 (accept_3_2 19 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 242 (accept_3_2 16 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 242 (accept_3_2 13 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 242 (accept_3_2 10 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 242 (Polychromatic418967fa.accept_17_8_13_4_1_6012 8 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 242 (accept_3_2 7 183 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 183 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 242 (accept_3_2 4 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 242 (accept_3_2 1 183 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 182
  242 (Eq.refl Bool.true) (allA_succ_of_gcd 60 182 242 2 30 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 182 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 182 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 242 2 29 91 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 182 242 2 28 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 182 242 (accept_3_2 55 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 242 2 27 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 242 (Polychromatic418967fa.accept_17_2_12_4_1_5987 53 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 242 2 26 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 242 2 25 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 242 (accept_3_2 49 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 242 2 24 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 242 (Polychromatic418967fa.accept_19_9_11_14_1_10626 47 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 242 2 23 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 242
  (Polychromatic418967fa.accept_19_7_11_14_1_11901 45 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 182 242 2 22 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 182 242 (accept_3_2 43 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 242 2 21 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 182 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 242 2 20 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 242 2 19 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 242 (accept_3_2 37 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 242 2 18 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 242 (Polychromatic418967fa.accept_16_3_6_2_1_4157 35 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 242 2 17 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 182 242 2 16 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 182 242 (accept_3_2 31 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 242 2 15 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 242 (Polychromatic418967fa.accept_21_8_14_11_1_11676 29 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 242 2 14 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 242
  (Polychromatic418967fa.accept_16_11_6_2_1_4155 27 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 242 2 13 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 242 (accept_3_2 25 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 242 2 12 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 182 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 242 2 11 91 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 242 2 10 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 242 (accept_3_2 19 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 242 2 9 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 242 (Polychromatic418967fa.accept_16_1_6_2_1_3100 17 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 242 2 8 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 242 2 7 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 242 (accept_3_2 13 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 242 2 6 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 242 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 242 2 5 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 242
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 242 2 4 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 242 (accept_3_2 7 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  242 2 3 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 182 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 242 2 2 91 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 182 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 242 2 1 91 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 242 (accept_3_2 1 182 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 181 242 (Eq.refl Bool.true)
  (allA_of_3_0 62 181 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 180 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 180 242 2 31 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 180 242 (accept_3_2 61 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 242 2 30 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 242 (Polychromatic418967fa.accept_25_9_5_17_1_14595 59 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 242 2 29 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 180 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 180 242 2 28 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 180 242 (accept_3_2 55 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 242 2 27 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 242 (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 242 2 26 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 242 2 25 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 242 (accept_3_2 49 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 242 2 24 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 242 (Polychromatic418967fa.accept_21_5_12_11_1_5429 47 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 242 2 23 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 180 242
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 180 242 2 22 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 180 242 (accept_3_2 43 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 242 2 21 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 180 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 242 2 20 90 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 242
  (Polychromatic418967fa.accept_19_1_9_14_1_526 39 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 180 242 2 19 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 180 242 (accept_3_2 37 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 242 2 18 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 242 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 242 2 17 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 242
  (Polychromatic418967fa.accept_29_4_6_10_1_14594 33 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 180 242 2 16 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 180 242 (accept_3_2 31 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 242 2 15 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 180 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 242 2 14 90 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 242 2 13 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 242 (accept_3_2 25 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 242 2 12 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 180 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 242 2 11 90 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 242
  (Polychromatic418967fa.accept_23_21_19_12_1_14593 21 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 180 242 2 10 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 180 242 (accept_3_2 19 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 242 2 9 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 242 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 242 2 8 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 180 242 2 7 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 242 (accept_3_2 13 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 242 2 6 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 242 (Polychromatic418967fa.accept_17_11_10_4_1_5955 11 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 242 2 5 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 242 2 4 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 242 (accept_3_2 7 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180
  242 2 3 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  180 242 (Polychromatic418967fa.accept_19_5_9_14_1_3505 5 180 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 242 2 2 90 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 242 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 180 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 242 2 1 90 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 242 (accept_3_2 1 180 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 179 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 179 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 242 (Polychromatic418967fa.accept_19_5_8_14_1_6384 62 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 242 (accept_3_2 61 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 242
  (Polychromatic418967fa.accept_19_3_8_14_1_14571 60 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 242 (Polychromatic418967fa.accept_13_7_10_8_1_567 59 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 242 (accept_3_2 58 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 179 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 242 (accept_3_2 55 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 242 (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 242 (accept_3_2 52 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 242
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 179 242 (accept_3_2 49 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 179 242 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 179 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 242 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 242 (accept_3_2 46 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 242 (accept_3_2 43 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 242 (Polychromatic418967fa.accept_15_12_14_2_1_3794 42 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 242 (accept_3_2 40 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 242
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 179 242 (accept_3_2 37 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 179 242 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 179 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 242 (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 242 (accept_3_2 34 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3
  33 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 242 (accept_3_2 31 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 242 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 242 (accept_3_2 28 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 242
  (Polychromatic418967fa.accept_19_7_8_14_1_13273 26 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 179 242 (accept_3_2 25 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 179 242 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 179 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 242
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 242 (accept_3_2 22 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 242 (accept_3_2 19 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 242 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 242 (accept_3_2 16 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 242 (Polychromatic418967fa.accept_17_14_9_4_1_3465 14 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 242 (accept_3_2 13 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 242 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 179
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 242
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 242 (accept_3_2 10 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 242 (accept_3_2 7 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 242 (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 179 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 242 (accept_3_2 4 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 242 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 242 (accept_3_2 1 179 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 179 242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 178 242 (Eq.refl Bool.true) (allA_of_3_0 65 178 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 66 177 242 (Eq.refl Bool.true) (allA_succ_of_accept 65 177 242 (Polychromatic418967fa.accept_6_5_3_2_1_68
  65 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 242 (accept_3_2 64
  177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 177 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 177 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 242 (accept_3_2 61 177 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 177 242 (Polychromatic418967fa.accept_16_12_1_2_1_2163 60 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 242 (accept_3_2 58 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 177 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 177 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 242 (accept_3_2 55 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 242 (accept_3_2 52 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 177 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 177 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 242 (accept_3_2 49 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 242 (accept_3_2 46 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 242 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 242 (accept_3_2 43 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 177
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 242 (accept_3_2 40 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 242 (accept_3_2 37 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 242 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 177 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 242 (accept_3_2 34 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 242 (accept_3_2 31 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 242 (accept_3_2 28 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 242 (accept_3_2 25 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 242 (accept_3_2 22 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 242 (accept_3_2 19 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 242 (accept_3_2 16 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 242 (accept_3_2 13 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 242 (accept_3_2 10 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 242 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 242 (Polychromatic418967fa.accept_17_8_7_4_1_8617 8 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 242 (accept_3_2 7 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 177 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 242 (accept_3_2 4 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 242 (accept_3_2 1 177 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 176 242 (Eq.refl Bool.true) (allA_succ_of_gcd 66 176 242 22 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 176 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 176 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 242 2 32 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 242
  (Polychromatic418967fa.accept_19_6_5_14_1_3582 63 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 176 242 2 31 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 176 242 (accept_3_2 61 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 242 2 30 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 176 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 242 2 29 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 242 2 28 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 176 242 11 5 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 176 242 2 27 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 176 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 242 2 26 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 242 2 25 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 242 (accept_3_2 49 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 242 2 24 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 176 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 242 2 23 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 242 22 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 176 242 (accept_3_2 43 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  176 242 2 21 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 176 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 176 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 242 2 20 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 39
  176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 176 242 2 19 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 176 242 (accept_3_2 37
  176 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 176 242 2 18 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 242
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 176 242 2 17 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 176 242 11 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 176 242 2 16 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 242 (accept_3_2 31 176 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 176 242 2 15 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 176 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 242 2 14 88 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 242
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 242 2 13 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 242 (accept_3_2 25 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 242 2 12 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 176 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 242 22 1 8 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 242 2 10 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 242 (accept_3_2 19 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 242 2 9 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 176 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 242 2 8 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 242 2 7 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 242 (accept_3_2 13 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 242 2 6 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 176 242 11 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 176 242 2 5 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 242 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 176 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 242 2 4 88 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 242 (accept_3_2 7
  176 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 242 2 3 88 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 176 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 242 2 2 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 176 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 242 2 1 88 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 242 (accept_3_2 1 176 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 175 242 (Eq.refl Bool.true) (allA_of_3_0 68 175 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 174 242
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 174 242 2 34 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 242 (accept_3_2 67 174 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 174 242 2 33 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 174 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 174 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 242 2 32 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 174 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 174 242 2 31 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 174 242 (accept_3_2 61 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 242 2 30 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 242 2 29 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 242 2 28 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 242 (accept_3_2 55 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 242 2 27 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 242 (Polychromatic418967fa.accept_13_1_5_8_1_207 53 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 242 2 26 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 242 2 25 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 242 (accept_3_2 49 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 242 2 24 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 242 2 23 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 242 2 22 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 242 (accept_3_2 43 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 242 2 21 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 242 2 20 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 242 2 19 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 242 (accept_3_2 37 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 242 2 18 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 242 (Polychromatic418967fa.accept_19_16_3_14_1_9212 35 174 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 242 2 17 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 242 2 16 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 242 (accept_3_2 31 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 242 2 15 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 242 2 14 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 242 2 13 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 242 (accept_3_2 25 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 242 2 12 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 242 2 11 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 242 2 10 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 242 (accept_3_2 19 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 242 2 9 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 242 2 8 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 242 2 7 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 242 (accept_3_2 13 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 242 2 6 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 174 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 242 2 5 87 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 242 2 4 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 242 (accept_3_2 7 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  242 2 3 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 174 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 242 2 2 87 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 242 2 1 87 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 242 (accept_3_2 1 174 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 173 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 173 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 173 242 (accept_3_2 67 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 242 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 242 (accept_3_2 64 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 242 (accept_3_2 61 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 242 (accept_3_2 58 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 242 (accept_3_2 55 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 242 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 173
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 242
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 53 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 242 (accept_3_2 52 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 242 (accept_3_2 49 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 242 (accept_3_2 46 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 242 (accept_3_2 43 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 242 (accept_3_2 40 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 242 (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 242 (accept_3_2 37 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 242 (accept_3_2 34 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 242 (accept_3_2 31 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 242 (accept_3_2 28 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 242 (Polychromatic418967fa.accept_19_7_2_14_1_3569 26 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 242 (accept_3_2 25 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 242 (accept_3_2 22 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 242 (accept_3_2 19 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 242 (Polychromatic418967fa.accept_20_18_13_2_1_10463 18 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 242
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 17 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 173 242 (accept_3_2 16 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 242 (accept_3_2 13 173 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 242 (Polychromatic418967fa.accept_9_3_2_8_1_108
  12 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 242 (accept_3_2 10 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 242 (accept_3_2 7 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 173 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 242 (accept_3_2 4 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 242 (accept_3_2 1 173 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 172 242 (Eq.refl Bool.true) (allA_of_3_0 71 172 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 171 242 (Eq.refl Bool.true) (allA_succ_of_accept 71 171 242 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 242 (accept_3_2 70
  171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 171 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 68 171 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 242 (accept_3_2 67 171 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 171 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 171 242 (accept_3_2 64 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 171 242 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 171 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 242 (accept_3_2 61 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 242 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 242 (accept_3_2 58 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 171 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 171 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 242 (accept_3_2 55 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 171
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 242 (accept_3_2 52 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 242 (Polychromatic418967fa.accept_23_5_10_12_1_14592 51 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 242 (accept_3_2 49 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 171 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 242 (accept_3_2 46 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 242 (Polychromatic418967fa.accept_23_21_10_12_1_14591 44 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 242 (accept_3_2 43 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 171
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 242 (accept_3_2 40 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 242 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 242 (accept_3_2 37 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 242 (accept_3_2 34 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 242 (Polychromatic418967fa.accept_13_6_2_8_1_1782 32 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 242 (accept_3_2 31 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 171
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 242 (accept_3_2 28 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 242 (accept_3_2 25 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 242 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 171
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 242 (accept_3_2 22 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 242 (accept_3_2 19 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 242 (accept_3_2 16 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 242 (Polychromatic418967fa.accept_17_14_1_4_1_2485 14 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 242 (accept_3_2 13 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 242 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 171
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 242 (accept_3_2 10 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 242 (accept_3_2 7 171 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 242 (accept_3_2 4 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 242 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 171 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 242 (Polychromatic418967fa.accept_23_2_10_12_1_14590 2 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 242 (accept_3_2 1 171 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 170 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 170 242 2 36 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 242 (Polychromatic418967fa.accept_13_6_1_8_1_1116 71 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 242 2 35 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 242 2 34 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 242 (accept_3_2 67 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 242 2 33 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 242 (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 242 2 32 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 242
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 242 2 31 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 242 (accept_3_2 61 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 242 2 30 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 242 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 242 2 29 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 242
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 242 2 28 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 242 (accept_3_2 55 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 242 2 27 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 242 (Polychromatic418967fa.accept_19_15_18_14_1_3564 53 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 242 2 26 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 242
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 51 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 242 2 25 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 242 (accept_3_2 49 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 242 2 24 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 170 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 242 2 23 85 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 242
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 242 2 22 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 242 (accept_3_2 43 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 242 2 21 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 170 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 242 2 20 85 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 242
  (Polychromatic418967fa.accept_19_1_18_14_1_6392 39 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 170 242 2 19 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 170 242 (accept_3_2 37 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 242 2 18 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 242 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 242 2 17 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 242 2 16 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 242 (accept_3_2 31 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 242 2 15 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 242 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 242 2 14 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 242 2 13 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 242 (accept_3_2 25 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 242 2 12 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 242 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 242 2 11 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 242
  (Polychromatic418967fa.accept_23_21_9_12_1_14589 21 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 170 242 2 10 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 170 242 (accept_3_2 19 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 242 2 9 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 242 (Polychromatic418967fa.accept_21_17_2_11_1_8656 17 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 242 2 8 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 242
  (Polychromatic418967fa.accept_19_15_18_14_1_3564 15 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 170 242 2 7 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 170 242 (accept_3_2 13 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 242 2 6 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 242 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 242 2 5 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 242
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 242 2 4 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 242 (accept_3_2 7 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  242 2 3 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 170 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 242 2 2 85 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 242 (Polychromatic418967fa.accept_15_3_5_2_1_2816 3 170 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 242 2 1 85 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 242 (accept_3_2 1 170 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 169 242 (Eq.refl
  Bool.true) (allA_of_3_0 74 169 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 168 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 168 242 2 37 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 242 (accept_3_2 73 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 242 2 36 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 242 (Polychromatic418967fa.accept_23_2_7_12_1_14588 71 168 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 242 2 35 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 242
  (Polychromatic418967fa.accept_13_4_12_8_1_197 69 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 168 242 2 34 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 242 (accept_3_2 67 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 242 2 33 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 242 2 32 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 242
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 63 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 168 242 2 31 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 168 242 (accept_3_2 61 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 242 2 30 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 242 2 29 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 242 2 28 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 242 (accept_3_2 55 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 242 2 27 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 242 (Polychromatic418967fa.accept_13_1_12_8_1_1818 53 168 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 242 2 26 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 242
  (Polychromatic418967fa.accept_19_13_16_14_1_3517 51 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 168 242 2 25 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 168 242 (accept_3_2 49 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 242 2 24 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 242 2 23 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 242 2 22 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 242 (accept_3_2 43 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 242 2 21 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 242 2 20 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 242 2 19 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 242 (accept_3_2 37 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 242 2 18 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 242 2 17 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 242
  (Polychromatic418967fa.accept_13_7_12_8_1_199 33 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 168 242 2 16 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 168 242 (accept_3_2 31 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 242 2 15 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 242 2 14 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 242
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 242 2 13 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 242 (accept_3_2 25 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 242 2 12 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 242 2 11 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 242 2 10 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 242 (accept_3_2 19 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 242 2 9 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 242 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 168 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 242 2 8 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 168 242 2 7 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 242 (accept_3_2 13 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 242 2 6 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 242 2 5 84 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 242
  (Polychromatic418967fa.accept_13_9_12_8_1_570 9 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 242 2 4 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 242 (accept_3_2 7 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  242 2 3 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 242 2 2 84 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 242 2 1 84 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 242 (accept_3_2 1 168 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 167 242 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 242 (accept_3_2 73
  167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 167 242 (Polychromatic418967fa.accept_13_6_11_8_1_1111 71 167 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 242 (accept_3_2 70 167 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 242 (Polychromatic418967fa.accept_7_5_6_4_1_117
  68 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 242 (accept_3_2 67
  167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 167 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 242 (accept_3_2 64 167 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 242
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 167 242 (accept_3_2 61 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 167 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 167 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 167 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 242 (accept_3_2 58 167 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 242 (accept_3_2 55 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 242 (accept_3_2 52 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 242
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 50 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 242 (accept_3_2 49 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 242 (accept_3_2 46 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 242 (accept_3_2 43 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 242 (accept_3_2 40 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 242 (accept_3_2 37 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 242 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 242 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 242 (accept_3_2 34 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 242 (accept_3_2 31 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 242 (accept_3_2 28 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 242 (accept_3_2 25 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 242 (accept_3_2 22 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 242 (accept_3_2 19 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 242 (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 242 (accept_3_2 16 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 242
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 242 (accept_3_2 13 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 242 (accept_3_2 10 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 242 (accept_3_2 7 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 242 (accept_3_2 4 167 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 242 (accept_3_2 1 167 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 166 242 (Eq.refl
  Bool.true) (allA_of_3_0 77 166 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 165 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 165 242 11 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 165 242 (accept_3_2 76 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 242 (accept_3_2 73 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 242 (Polychromatic418967fa.accept_13_7_9_8_1_188
  72 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 242 (accept_3_2 70 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 165 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 165 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 242 (accept_3_2 67 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 242 11 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 242 (accept_3_2 64 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 242
  (Polychromatic418967fa.accept_19_5_13_14_1_6366 62 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 165 242 (accept_3_2 61 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 165 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 242 (accept_3_2 58 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 242 (Polychromatic418967fa.accept_10_7_5_2_1_880
  57 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 165 242 11 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 165 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 242 (accept_3_2 52
  165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 165 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 242 (accept_3_2 49 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 165 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 165 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 242 (accept_3_2 46 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 242 (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 165 242 11 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 165 242 (accept_3_2 43 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 242 (accept_3_2 40 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 242 (accept_3_2 37 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 242 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 242 (accept_3_2 34 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 242 11 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 242 (accept_3_2 31 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 242 (Polychromatic418967fa.accept_12_6_9_2_1_311
  30 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 242 (accept_3_2 28 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 242 (Polychromatic418967fa.accept_17_9_12_4_1_3468 26 165 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 242 (accept_3_2 25 165 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 165 242 11 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 165 242 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 165 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 242 (accept_3_2 19 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 242 (accept_3_2 16 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 242 (accept_3_2 13 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 242 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 165 242 11 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 10 165 242 (accept_3_2 10 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 165 242 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 165 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 242 (accept_3_2 7 165 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 6
  165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 242 (accept_3_2 4 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 242 (accept_3_2 1 165 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 164 242 (Eq.refl Bool.true) (allA_succ_of_gcd 78 164 242 2 39 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 164 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 164 242 2 38 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 164 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 164 242 2 37 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 164 242 (accept_3_2 73 164 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 164 242 2 36 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 164 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 71
  164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 242 2 35 82 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 242 2 34 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 242 (accept_3_2 67 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 242 2 33 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 242 2 32 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 242
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 242 2 31 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 242 (accept_3_2 61 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 242 2 30 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 242 2 29 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 242 2 28 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 242 (accept_3_2 55 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 242 2 27 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 242 2 26 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 242 2 25 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 242 (accept_3_2 49 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 242 2 24 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 242 2 23 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 242
  (Polychromatic418967fa.accept_19_7_12_14_1_9206 45 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 164 242 2 22 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 164 242 (accept_3_2 43 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 242 2 21 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 242 2 20 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 242 2 19 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 242 (accept_3_2 37 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 242 2 18 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 164 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 242 2 17 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 242 2 16 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 242 (accept_3_2 31 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 242 2 15 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 242 2 14 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 242 2 13 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 242 (accept_3_2 25 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 242 2 12 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 242 2 11 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 242 2 10 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 242 (accept_3_2 19 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 242 2 9 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 164 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 242 2 8 82 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 242 2 7 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 242 (accept_3_2 13 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 242 2 6 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 164 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 242 2 5 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 242
  (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 242 2 4 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 242 (accept_3_2 7 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  242 2 3 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 242 2 2 82 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 164 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 242 2 1 82 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 242 (accept_3_2 1 164 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 163 242 (Eq.refl
  Bool.true) (allA_of_3_0 80 163 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 162 242 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 162 242 2 40 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 162 242 (accept_3_2 79 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 242 2 39 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 242 (Polychromatic418967fa.accept_19_1_10_14_1_3597 77 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 242 2 38 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 162 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 162 242 2 37 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 242 (accept_3_2 73 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 242 2 36 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 242 (Polychromatic418967fa.accept_24_23_18_2_1_14587 71 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 242 2 35 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 242 2 34 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 242 (accept_3_2 67 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 242 2 33 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 242 (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 242 2 32 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 242 2 31 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 242 (accept_3_2 61 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 242 2 30 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 162 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 242 2 29 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 242 2 28 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 242 (accept_3_2 55 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 242 2 27 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 242 (Polychromatic418967fa.accept_13_1_6_8_1_208 53 162 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 242 2 26 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 242 2 25 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 242 (accept_3_2 49 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 242 2 24 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 162 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 242 2 23 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 242 2 22 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 242 (accept_3_2 43 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 242 2 21 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 242 (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 242 2 20 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 242 2 19 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 242 (accept_3_2 37 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 242 2 18 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 242 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 242 2 17 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 242 2 16 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 242 (accept_3_2 31 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 242 2 15 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 242 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 242 2 14 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 242 2 13 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 242 (accept_3_2 25 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 242 2 12 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 242 (Polychromatic418967fa.accept_19_4_10_14_1_7833 23 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 242 2 11 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 242 2 10 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 242 (accept_3_2 19 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 242 2 9 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 162 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 242 2 8 81 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 242 2 7 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 242 (accept_3_2 13 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 242 2 6 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 242 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 242 2 5 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 242 2 4 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 242 (accept_3_2 7 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  242 2 3 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 162 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 242 2 2 81 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 242 2 1 81 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 242 (accept_3_2 1 162 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 161 242 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 242 (Polychromatic418967fa.accept_12_8_5_2_1_746
  80 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 161 242 (accept_3_2 79
  161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 161 242
  (Polychromatic418967fa.accept_25_3_11_17_1_14586 78 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 242 (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 242 (accept_3_2 76 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 242
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 74 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 242 (accept_3_2 73 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 242 (Polychromatic418967fa.accept_31_10_6_25_1_14585 72 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 242 (accept_3_2 70 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 68 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 242 (accept_3_2 67 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 242 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 242 (accept_3_2 64 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 242
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 62 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 242 (accept_3_2 61 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 242 (Polychromatic418967fa.accept_16_12_1_2_1_2163 60 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 242 (accept_3_2 58 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 242
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 242 (accept_3_2 55 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 242 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 242 (Polychromatic418967fa.accept_10_3_1_2_1_521 53 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 242 (accept_3_2 52 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 242
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 242 (accept_3_2 49 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 242 (Polychromatic418967fa.accept_21_6_14_11_1_10103 48 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 242 (accept_3_2 46 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 242 (accept_3_2 43 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 242 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 242 (Polychromatic418967fa.accept_16_9_1_2_1_2126 41 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 242 (accept_3_2 40 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 242
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 242 (accept_3_2 37 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 242 (accept_3_2 34 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 242 (accept_3_2 31 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 242 (Polychromatic418967fa.accept_17_13_8_4_1_2514 30 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 242 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 242 (accept_3_2 28 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 242
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 242 (accept_3_2 25 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 242 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 242 (accept_3_2 22 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 242 (accept_3_2 19 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 242 (Polychromatic418967fa.accept_17_1_8_4_1_1519 18 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 242 (Polychromatic418967fa.accept_14_3_7_4_1_118 17 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 242 (accept_3_2 16 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 242
  (Polychromatic418967fa.accept_13_1_5_8_1_207 14 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 242 (accept_3_2 13 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 242 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 242 (accept_3_2 10 161 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 242 (accept_3_2 7 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 242 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 242 (accept_3_2 4 161 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 242
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 242 (accept_3_2 1 161 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 160 242 (Eq.refl
  Bool.true) (allA_of_3_0 83 160 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 159 242 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 159 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 242 (accept_3_2 82 159 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 242
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 80 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 159 242 (accept_3_2 79 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 159 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 242 (accept_3_2 76 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 159 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 159 242 (accept_3_2 73 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 159 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 242 (accept_3_2 70 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 242 (accept_3_2 67 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 242 (accept_3_2 64 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 242 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 159 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 242 (accept_3_2 61 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 242 (Polychromatic418967fa.accept_16_12_15_2_1_6473 60 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 242 (accept_3_2 58 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 242 (accept_3_2 55 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 242 (accept_3_2 52 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 242 (accept_3_2 49 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 242 (accept_3_2 46 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 242 (accept_3_2 43 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 242 (accept_3_2 40 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 242 (accept_3_2 37 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 242 (accept_3_2 34 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 242 (accept_3_2 31 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 242 (accept_3_2 28 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 242
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 242 (accept_3_2 25 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 242 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 242 (accept_3_2 22 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 242 (accept_3_2 19 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 242 (accept_3_2 16 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 242 (accept_3_2 13 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 242 (accept_3_2 10 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 242 (accept_3_2 7 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 242 (accept_3_2 4 159 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 242 (accept_3_2 1 159 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 158 242
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 158 242 2 42 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 158 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 158 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 242 2 41 79 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 242
  (Polychromatic418967fa.accept_15_6_8_2_1_104 81 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 242 2 40 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 242 (accept_3_2 79 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 242 2 39 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 242 (Polychromatic418967fa.accept_18_5_14_8_1_2966 77 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 242 2 38 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 242 2 37 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 242 (accept_3_2 73 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 242 2 36 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 242 (Polychromatic418967fa.accept_13_6_2_8_1_1782 71 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 242 2 35 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 242 2 34 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 242 (accept_3_2 67 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 242 2 33 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 158 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 242 2 32 79 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 242
  (Polychromatic418967fa.accept_20_3_18_2_1_5918 63 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 242 2 31 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 242 (accept_3_2 61 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 242 2 30 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 242 (Polychromatic418967fa.accept_13_7_2_8_1_1746 59 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 242 2 29 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 242 2 28 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 242 (accept_3_2 55 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 242 2 27 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 242 (Polychromatic418967fa.accept_20_13_18_2_1_10452 53 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 242 2 26 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 242 2 25 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 242 (accept_3_2 49 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 242 2 24 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 158 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 242 2 23 79 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 242 2 22 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 242 (accept_3_2 43 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 242 2 21 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 242 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 242 2 20 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 242 2 19 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 242 (accept_3_2 37 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 242 2 18 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 158 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 242 2 17 79 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 242 2 16 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 242 (accept_3_2 31 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 242 2 15 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 242 2 14 79 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 242
  (Polychromatic418967fa.accept_19_8_6_14_1_5009 27 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 242 2 13 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 242 (accept_3_2 25 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 242 2 12 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 242 (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 242 2 11 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 242 2 10 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 242 (accept_3_2 19 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 242 2 9 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 242 (Polychromatic418967fa.accept_20_17_18_2_1_8937 17 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 242 2 8 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 242 2 7 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 242 (accept_3_2 13 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 242 2 6 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 242 2 5 79 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 242
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 242 2 4 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 242 (accept_3_2 7 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  242 2 3 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 158 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 242 2 2 79 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 158 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 242 2 1 79 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 242 (accept_3_2 1 158 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 157 242
  (Eq.refl Bool.true) (allA_of_3_0 86 157 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 156 242 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 156 242 2 43 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 156 242 (accept_3_2 85 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 242 2 42 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 242 2 41 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 156 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 156 242 2 40 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 156 242 (accept_3_2 79 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 242 2 39 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 242 2 38 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 156 242 2 37 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 242 (accept_3_2 73 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 242 2 36 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 242 2 35 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 242 2 34 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 242 (accept_3_2 67 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 242 2 33 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 242 2 32 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 242
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 63 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 156 242 2 31 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 242 (accept_3_2 61 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 242 2 30 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 242 2 29 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 242
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 57 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 242 2 28 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 242 (accept_3_2 55 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 242 2 27 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 156 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 242 2 26 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 242 2 25 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 242 (accept_3_2 49 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 242 2 24 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 242 2 23 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 242
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 242 2 22 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 242 (accept_3_2 43 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 242 2 21 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 242 2 20 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 242
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 39 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 242 2 19 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 242 (accept_3_2 37 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 242 2 18 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 242 (Polychromatic418967fa.accept_25_10_6_17_1_7346 35 156 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 242 2 17 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 242 2 16 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 242 (accept_3_2 31 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 242 2 15 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 242 2 14 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 242 2 13 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 242 (accept_3_2 25 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 242 2 12 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 242 2 11 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 242 2 10 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 242 (accept_3_2 19 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 242 2 9 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 242 (Polychromatic418967fa.accept_16_1_12_2_1_2136 17 156 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 242 2 8 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 242 2 7 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 242 (accept_3_2 13 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 242 2 6 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 242 2 5 78 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 242
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 242 2 4 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 242 (accept_3_2 7 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  242 2 3 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 242 2 2 78 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 242 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 156 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 242 2 1 78 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 242 (accept_3_2 1 156 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 155 242
  (Eq.refl Bool.true) (allA_succ_of_accept 87 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 155 242 (accept_3_2 85 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 155 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 155 242 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 242 (accept_3_2 82 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 242 (accept_3_2 79 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 242 (accept_3_2 76 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 242
  (Polychromatic418967fa.accept_13_9_12_8_1_570 74 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 242 (accept_3_2 73 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 242 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 242 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 242 (accept_3_2 70 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 155 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 242 (accept_3_2 67 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 242 (accept_3_2 64 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 242
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 62 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 155 242 (accept_3_2 61 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 155 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 155 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 155 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 242 (accept_3_2 58 155 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 242 (accept_3_2 55 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 242 (accept_3_2 52 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 242 (accept_3_2 49 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 242 (accept_3_2 46 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 242 (accept_3_2 43 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 242 (accept_3_2 40 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 242 (accept_3_2 37 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 242 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 242 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 242 (accept_3_2 34 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 242 (accept_3_2 31 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 242 (accept_3_2 28 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 242 (accept_3_2 25 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 242 (accept_3_2 22 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 242 (accept_3_2 19 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 242 (accept_3_2 16 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 242 (accept_3_2 13 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 242 (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 242 (accept_3_2 10 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 242
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 242 (accept_3_2 7 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 242 (accept_3_2 4 155 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 242
  (Polychromatic418967fa.accept_27_2_20_26_1_14584 2 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 155 242 (accept_3_2 1 155 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  155 242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 154 242
  (Eq.refl Bool.true) (allA_of_3_0 89 154 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 153 242 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 242 (accept_3_2 88 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 242 (accept_3_2 85 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 153 242 (Polychromatic418967fa.accept_25_9_3_17_1_14583 84 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 242 (accept_3_2 82 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 242 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 80 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 242 (accept_3_2 79 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 242 (accept_3_2 76 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 242
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 242 (accept_3_2 73 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 153 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 242 (accept_3_2 70 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 242 (Polychromatic418967fa.accept_13_4_10_8_1_1817 69 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 242 (accept_3_2 67 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 242 (accept_3_2 64 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 242
  (Polychromatic418967fa.accept_21_20_6_11_1_2623 62 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 153 242 (accept_3_2 61 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 153 242 (Polychromatic418967fa.accept_16_12_9_2_1_8989 60 153 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 242 (accept_3_2 58 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 242
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 242 (Polychromatic418967fa.accept_13_4_10_8_1_1817 56 153 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 242 (accept_3_2 55 153 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 242 (accept_3_2 52
  153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 242 (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 242 (accept_3_2 49 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 242 (Polychromatic418967fa.accept_19_10_1_14_1_9224 48 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 242 (accept_3_2 46 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 242 (accept_3_2 43 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 242 (accept_3_2 40 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 242 (accept_3_2 37 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 242 (Polychromatic418967fa.accept_19_17_1_14_1_6360 36 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 242 (accept_3_2 34 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 242 (Polychromatic418967fa.accept_19_13_1_14_1_3634 32 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 242 (accept_3_2 31 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 242 (accept_3_2 28 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 242 (accept_3_2 25 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 242 (accept_3_2 22 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 242 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 242 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 242 (accept_3_2 19 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 153
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 242 (accept_3_2 16 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 242 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 242 (accept_3_2 13 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 242 (accept_3_2 10 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 242 (Polychromatic418967fa.accept_25_8_3_17_1_14582 8 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 242 (accept_3_2 7 153 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 242 (accept_3_2 4 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 242 (accept_3_2 1 153 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 152 242
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 152 242 2 45 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 152 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 152 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 242 2 44 76 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 242
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 87 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 242 2 43 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 242 (accept_3_2 85 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 242 2 42 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 242 2 41 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 242
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 81 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 242 2 40 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 242 (accept_3_2 79 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 242 2 39 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 242 2 38 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 242
  (Polychromatic418967fa.accept_21_12_5_11_1_14581 75 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 152 242 2 37 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 152 242 (accept_3_2 73 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 242 2 36 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 242 2 35 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 242 2 34 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 242 (accept_3_2 67 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 242 2 33 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 242 2 32 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 242
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 242 2 31 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 242 (accept_3_2 61 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 242 2 30 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 152 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 242 2 29 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 242 2 28 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 242 (accept_3_2 55 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 242 2 27 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 242 2 26 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 242 2 25 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 242 (accept_3_2 49 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 242 2 24 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 152 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 242 2 23 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 242
  (Polychromatic418967fa.accept_27_18_17_26_1_10801 45 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 152 242 2 22 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 152 242 (accept_3_2 43 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 242 2 21 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 242 2 20 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 242
  (Polychromatic418967fa.accept_17_5_16_4_1_4734 39 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 242 2 19 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 242 (accept_3_2 37 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 242 2 18 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 152 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 242 2 17 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 242
  (Polychromatic418967fa.accept_13_7_9_8_1_188 33 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 242 2 16 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 242 (accept_3_2 31 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 242 2 15 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 242 2 14 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 242 2 13 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 242 (accept_3_2 25 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 242 2 12 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 242 2 11 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 242
  (Polychromatic418967fa.accept_23_21_14_12_1_14580 21 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 152 242 2 10 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 152 242 (accept_3_2 19 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 242 2 9 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 152 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 242 2 8 76 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 242 2 7 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 242 (accept_3_2 13 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 242 2 6 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 152 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 242 2 5 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 242 2 4 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 242 (accept_3_2 7 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  242 2 3 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 152 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 242 2 2 76 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 242 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 152 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 242 2 1 76 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 242 (accept_3_2 1 152 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 151 242
  (Eq.refl Bool.true) (allA_of_3_0 92 151 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 150 242 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 150 242 2 46 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 150 242 (accept_3_2 91 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 242 2 45 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 242 (Polychromatic418967fa.accept_16_9_6_2_1_3101 89 150 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 242 2 44 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 242 2 43 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 150 242 (accept_3_2 85 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 242 2 42 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 242 2 41 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 242 2 40 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 242 (accept_3_2 79 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 242 2 39 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 242 2 38 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 150 242 2 37 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 242 (accept_3_2 73 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 242 2 36 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 242 2 35 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 242 2 34 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 242 (accept_3_2 67 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 242 2 33 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 242 2 32 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 242 2 31 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 242 (accept_3_2 61 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 242 2 30 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 242 2 29 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 242 2 28 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 242 (accept_3_2 55 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 242 2 27 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 242 (Polychromatic418967fa.accept_13_1_7_8_1_1796 53 150 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 242 2 26 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 242 2 25 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 242 (accept_3_2 49 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 242 2 24 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 242 2 23 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 242 2 22 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 242 (accept_3_2 43 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 242 2 21 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 242 2 20 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 242 2 19 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 242 (accept_3_2 37 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 242 2 18 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 242 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 150 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 242 2 17 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 242 2 16 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 242 (accept_3_2 31 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 242 2 15 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 242 2 14 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 242 2 13 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 242 (accept_3_2 25 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 242 2 12 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 242 2 11 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 242 2 10 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 242 (accept_3_2 19 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 242 2 9 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 242 (Polychromatic418967fa.accept_16_1_6_2_1_3100 17 150 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 242 2 8 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 242
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 242 2 7 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 242 (accept_3_2 13 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 242 2 6 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 242 2 5 75 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 242 2 4 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 242 (accept_3_2 7 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  242 2 3 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 150 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 242 2 2 75 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 242 2 1 75 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 242 (accept_3_2 1 150 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 149
  242 (Eq.refl Bool.true) (allA_succ_of_accept 93 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 149 242 (accept_3_2 91 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 149 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 149 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 242 (accept_3_2 88 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 242
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 86 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 149 242 (accept_3_2 85 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 149 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 242 (accept_3_2 82 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 80 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 242 (accept_3_2 79 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 242 (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 242 (accept_3_2 76 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 149 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 242 (accept_3_2 73 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 242 (accept_3_2 70 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 242 (accept_3_2 67 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 242 (accept_3_2 64 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 242 (accept_3_2 61 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 242 (accept_3_2 58 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 242 (accept_3_2 55 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 242 (Polychromatic418967fa.accept_13_1_6_8_1_208 53 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 242 (accept_3_2 52 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 242
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 50 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 242 (accept_3_2 49 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 242 (accept_3_2 46 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 242 (accept_3_2 43 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 242 (accept_3_2 40 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 242 (accept_3_2 37 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 242 (Polychromatic418967fa.accept_19_17_16_14_1_10604 36 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 242 (accept_3_2 34 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 242 (accept_3_2 31 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 242 (accept_3_2 28 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 242 (accept_3_2 25 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 242 (accept_3_2 22 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 242 (accept_3_2 19 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 242 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 242 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 242 (accept_3_2 16 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 242
  (Polychromatic418967fa.accept_13_1_6_8_1_208 14 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 242 (accept_3_2 13 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 242 (accept_3_2 10 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 242 (accept_3_2 7 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 242 (accept_3_2 4 149 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 242 (accept_3_2 1 149 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 148
  242 (Eq.refl Bool.true) (allA_of_3_0 95 148 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 147 242
  (Eq.refl Bool.true) (allA_succ_of_accept 95 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 242 (accept_3_2 94 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 147 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 147 242 (accept_3_2 91 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 147 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 242 (accept_3_2 88 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 147 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 147 242 (accept_3_2 85 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 147 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 242 (accept_3_2 82 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 242
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 80 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 242 (accept_3_2 79 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 242 (accept_3_2 76 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 242 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 147 242 (accept_3_2 73 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 147 242 (Polychromatic418967fa.accept_20_12_7_2_1_4448 72 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 242 (accept_3_2 70 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 242 (accept_3_2 67 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 147 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 242 (accept_3_2 64 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 242 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 147 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 242
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 62 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 242 (accept_3_2 61 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 242 (accept_3_2 58 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 242 (accept_3_2 55 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 242 (accept_3_2 52 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 242 (accept_3_2 49 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 147 242 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 242 (accept_3_2 46 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 242
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 242 (accept_3_2 43 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 242 (accept_3_2 40 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 242 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 242 (accept_3_2 37 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 242 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 242 (accept_3_2 34 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 242 (accept_3_2 31 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 242 (accept_3_2 28 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 242 (Polychromatic418967fa.accept_17_10_11_4_1_2522 27 147 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 242
  (Polychromatic418967fa.accept_23_3_9_12_1_14579 26 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 147 242 (accept_3_2 25 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 242 (accept_3_2 22 147 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 242 (accept_3_2 19 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 242 (accept_3_2 16 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 242
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 242 (accept_3_2 13 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 242 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 242 (accept_3_2 10 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 242
  (Polychromatic418967fa.accept_24_8_3_2_1_7809 8 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 242 (accept_3_2 7 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 242 (accept_3_2 4 147 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 242 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 147 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 242
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 242 (accept_3_2 1 147 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 146
  242 (Eq.refl Bool.true) (allA_succ_of_gcd 96 146 242 2 48 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 146 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 146 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 242 2 47 73 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 242 2 46 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 242 (accept_3_2 91 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 242 2 45 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 242 2 44 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 242 2 43 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 242 (accept_3_2 85 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 242 2 42 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 242 (Polychromatic418967fa.accept_13_5_3_8_1_1117 83 146 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 242 2 41 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 242 2 40 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 242 (accept_3_2 79 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 242 2 39 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 242 2 38 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 242 2 37 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 242 (accept_3_2 73 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 242 2 36 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 242 2 35 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 242 2 34 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 242 (accept_3_2 67 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 242 2 33 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 242 2 32 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 242
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 242 2 31 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 242 (accept_3_2 61 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 242 2 30 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 242 2 29 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 242 2 28 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 242 (accept_3_2 55 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 242 2 27 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 242 (Polychromatic418967fa.accept_18_17_2_8_1_6800 53 146 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 242 2 26 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 242 2 25 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 242 (accept_3_2 49 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 242 2 24 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 242 2 23 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 242 2 22 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 242 (accept_3_2 43 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 242 2 21 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 242 2 20 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 242 2 19 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 242 (accept_3_2 37 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 242 2 18 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 242 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 242 2 17 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 242 2 16 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 242 (accept_3_2 31 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 242 2 15 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 242 (Polychromatic418967fa.accept_21_8_20_11_1_7025 29 146 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 242 2 14 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 242
  (Polychromatic418967fa.accept_19_8_13_14_1_2373 27 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 146 242 2 13 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 146 242 (accept_3_2 25 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 242 2 12 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 242 2 11 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 242 2 10 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 242 (accept_3_2 19 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 242 2 9 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 242 2 8 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 242 2 7 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 242 (accept_3_2 13 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 242 2 6 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 146 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 242 2 5 73 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 242 2 4 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 242 (accept_3_2 7 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  242 2 3 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 146 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 242 2 2 73 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 146 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 242 2 1 73 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 242 (accept_3_2 1 146 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  145 242 (Eq.refl Bool.true) (allA_of_3_0 98 145 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 144 242
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 242 2 49 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 242 (accept_3_2 97 144 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 144 242 2 48 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 144 242 (Polychromatic418967fa.accept_20_15_4_2_1_5914 95 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 242 2 47 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 242
  (Polychromatic418967fa.accept_19_17_11_14_1_7858 93 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 144 242 2 46 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 144 242 (accept_3_2 91 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 242 2 45 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 242 (Polychromatic418967fa.accept_13_11_1_8_1_1776 89 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 242 2 44 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 87 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 144 242 2 43 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 144 242 (accept_3_2 85 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 242 2 42 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 242 (Polychromatic418967fa.accept_13_5_1_8_1_1115 83 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 242 2 41 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 242
  (Polychromatic418967fa.accept_17_13_8_4_1_2514 81 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 242 2 40 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 242 (accept_3_2 79 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 242 2 39 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 144 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 242 2 38 72 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 242
  (Polychromatic418967fa.accept_17_7_8_4_1_1520 75 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 144 242 2 37 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 242 (accept_3_2 73 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 242 2 36 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 242 (Polychromatic418967fa.accept_13_6_1_8_1_1116 71 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 242 2 35 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 242
  (Polychromatic418967fa.accept_17_1_8_4_1_1519 69 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 242 2 34 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 242 (accept_3_2 67 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 242 2 33 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 242 (Polychromatic418967fa.accept_20_5_4_2_1_5912 65 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 242 2 32 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 242
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 242 2 31 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 242 (accept_3_2 61 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 242 2 30 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 242 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 242 2 29 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 242 2 28 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 242 (accept_3_2 55 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 242 2 27 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 242 (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 242 2 26 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 242
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 51 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 242 2 25 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 242 (accept_3_2 49 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 242 2 24 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 144 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 242 2 23 72 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 242
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 242 2 22 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 242 (accept_3_2 43 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 242 2 21 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 242 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 242 2 20 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 242
  (Polychromatic418967fa.accept_20_19_4_2_1_8946 39 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 242 2 19 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 242 (accept_3_2 37 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 242 2 18 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 242 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 242 2 17 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 242
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 242 2 16 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 242 (accept_3_2 31 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 242 2 15 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 242 (Polychromatic418967fa.accept_17_12_8_4_1_2518 29 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 242 2 14 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 242 2 13 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 242 (accept_3_2 25 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 242 2 12 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 242 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 242 2 11 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 242
  (Polychromatic418967fa.accept_26_21_14_8_1_12713 21 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 144 242 2 10 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 144 242 (accept_3_2 19 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 242 2 9 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 242 2 8 72 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 242
  (Polychromatic418967fa.accept_19_15_11_14_1_11940 15 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 242 2 7 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 242 (accept_3_2 13 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 242 2 6 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 242 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 242 2 5 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 242
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 242 2 4 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 242 (accept_3_2 7 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  242 2 3 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 242 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 144 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 242 2 2 72 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 242 (Polychromatic418967fa.accept_19_3_11_14_1_7838 3 144 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 242 2 1 72 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 242 (accept_3_2 1 144 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  143 242 (Eq.refl Bool.true) (allA_succ_of_gcd 99 143 242 11 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 143 242 (Polychromatic418967fa.accept_20_18_3_2_1_5929 98 143
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 242 (accept_3_2 97 143
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 242
  (Polychromatic418967fa.accept_15_6_8_2_1_104 96 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 143 242 (Polychromatic418967fa.accept_10_5_3_2_1_899 95 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 242 (accept_3_2 94 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128
  92 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 242 (accept_3_2 91
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 242
  (Polychromatic418967fa.accept_7_6_3_4_1_294 90 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 143 242 11 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 87
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 242
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 86 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 143 242 (accept_3_2 85 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 143 242 (Polychromatic418967fa.accept_15_9_8_2_1_1109 84 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 242 (accept_3_2 82 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 242 (accept_3_2 79 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 143 242 11 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 143 242 (accept_3_2 76 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 242 (Polychromatic418967fa.accept_18_2_17_8_1_1893 74 143
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 242 (accept_3_2 73 143
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 242
  (Polychromatic418967fa.accept_19_15_10_14_1_3652 72 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 242 (accept_3_2 70 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 242 (accept_3_2 67 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66
  143 242 11 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 242 (accept_3_2 64 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 242 (Polychromatic418967fa.accept_7_6_3_4_1_294
  62 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 242 (accept_3_2 61
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 242
  (Polychromatic418967fa.accept_16_12_15_2_1_6473 60 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 242 (Polychromatic418967fa.accept_17_8_7_4_1_8617 59 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 242 (accept_3_2 58 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 242
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 143 242 11 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 143 242 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 242 (accept_3_2 52 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 242 (accept_3_2 49 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 242
  (Polychromatic418967fa.accept_21_5_17_11_1_7021 47 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 143 242 (accept_3_2 46 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 143 242 11 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 143 242 (accept_3_2 43 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 242 (Polychromatic418967fa.accept_17_8_7_4_1_8617 42 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 242 (accept_3_2 40 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 242 (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 242 (accept_3_2 37 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 242
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 242 (accept_3_2 34 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33
  143 242 11 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 143 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 242 (accept_3_2 31 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 143 242 (Polychromatic418967fa.accept_20_10_3_2_1_4444 30 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 242 (accept_3_2 28 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 242 (Polychromatic418967fa.accept_19_7_10_14_1_3599 26 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 242 (accept_3_2 25 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 242 (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 143
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 242
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 143 242 11 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 242 (Polychromatic418967fa.accept_7_6_3_4_1_294
  20 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 242 (accept_3_2 19
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 242
  (Polychromatic418967fa.accept_19_18_10_14_1_2392 18 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 242 (accept_3_2 16 143 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 242
  (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 242 (accept_3_2 13 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 242 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 143 242 11 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 10 143 242 (accept_3_2 10 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 242 (accept_3_2 7 143 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 242 (accept_3_2 4 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 242 (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 242 (accept_3_2 1 143 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 143
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 142 242 (Eq.refl Bool.true) (allA_of_3_0 101 142 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 141
  242 (Eq.refl Bool.true) (allA_succ_of_accept 101 141 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 141 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 141 242 (accept_3_2 100 141 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 99
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 242
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 98 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 141 242 (accept_3_2 97 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 141 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 242 (accept_3_2 94 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 141 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 141 242 (accept_3_2 91 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 141 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 141 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 242 (accept_3_2 88 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 242 (accept_3_2 85 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 141 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 242 (accept_3_2 82 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 242 (Polychromatic418967fa.accept_13_3_11_8_1_1094 81 141 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 141 242 (accept_3_2 79 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 141 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 141 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 242 (accept_3_2 76 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 242 (accept_3_2 73 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 141 242 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 242 (accept_3_2 70 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 242 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 242 (accept_3_2 67 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 141 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 141 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 242 (accept_3_2 64 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 242
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 141 242 (accept_3_2 61 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 141 242 (Polychromatic418967fa.accept_19_3_8_14_1_14571 60 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 242 (accept_3_2 58
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 242 (accept_3_2 55 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 242 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 242 (accept_3_2 52
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 242 (accept_3_2 49 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 242 (accept_3_2 46
  141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 242 (Polychromatic418967fa.accept_19_6_8_14_1_2351 44 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 242 (accept_3_2 43 141 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 242 (accept_3_2 40 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 242 (accept_3_2 37 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 242 (accept_3_2 34 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 242 (accept_3_2 31 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 242 (accept_3_2 28 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 242 (accept_3_2 25 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 242 (accept_3_2 22 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 242 (accept_3_2 19 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 242 (accept_3_2 16 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 242 (accept_3_2 13 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 242 (accept_3_2 10 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 242 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 242 (accept_3_2 7 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 141 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 242 (accept_3_2 4 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 242 (accept_3_2 1 141 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 140 242 (Eq.refl Bool.true) (allA_succ_of_gcd 102 140 242 2 51 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11
  101 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 242 2 50 70 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 242
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 99 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 140 242 2 49 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 140 242 (accept_3_2 97 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 242 2 48 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 95 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 242 2 47 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 93 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 242 2 46 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 242 (accept_3_2 91 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 242 2 45 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 242 2 44 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 242 2 43 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 242 (accept_3_2 85 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 242 2 42 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 242 2 41 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 242
  (Polychromatic418967fa.accept_16_1_12_2_1_2136 81 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 242 2 40 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 242 (accept_3_2 79 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 242 2 39 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 242 2 38 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 242 2 37 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 242 (accept_3_2 73 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 242 2 36 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 242 2 35 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 242 2 34 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 242 (accept_3_2 67 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 242 2 33 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 242 2 32 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 242
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 242 2 31 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 242 (accept_3_2 61 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 242 2 30 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 242 2 29 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 242 2 28 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 242 (accept_3_2 55 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 242 2 27 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 242 2 26 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 242 2 25 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 242 (accept_3_2 49 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 242 2 24 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 242 2 23 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 242
  (Polychromatic418967fa.accept_21_3_14_11_1_14578 45 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 242 2 22 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 242 (accept_3_2 43 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 242 2 21 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 242 2 20 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 242 2 19 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 242 (accept_3_2 37 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 242 2 18 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 242 2 17 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 242 2 16 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 242 (accept_3_2 31 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 242 2 15 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 242 2 14 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 242
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 242 2 13 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 242 (accept_3_2 25 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 242 2 12 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 242 2 11 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 242
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 242 2 10 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 242 (accept_3_2 19 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 242 2 9 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 242 2 8 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 242
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 242 2 7 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 242 (accept_3_2 13 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 242 2 6 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 140 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 242 2 5 70 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 242
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 242 2 4 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 242 (accept_3_2 7 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  242 2 3 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 242 2 2 70 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 140 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 242 2 1 70 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 242 (accept_3_2 1 140 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 139 242 (Eq.refl Bool.true) (allA_of_3_0 104 139 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 138
  242 (Eq.refl Bool.true) (allA_succ_of_gcd 104 138 242 2 52 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 242 (accept_3_2 103 138 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 138 242 2 51 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 138 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 138 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 242 2 50 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 138 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 138 242 2 49 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 138 242 (accept_3_2 97 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 242 2 48 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 242 2 47 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 242 2 46 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 242 (accept_3_2 91 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 242 2 45 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 242 (Polychromatic418967fa.accept_15_14_3_2_1_2811 89 138 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 242 2 44 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 87 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 242 2 43 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 242 (accept_3_2 85 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 242 2 42 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 242 2 41 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 242 2 40 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 242 (accept_3_2 79 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 242 2 39 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 242 2 38 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 75 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 242 2 37 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 242 (accept_3_2 73 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 242 2 36 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 242 2 35 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 242 2 34 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 242 (accept_3_2 67 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 242 2 33 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 242 2 32 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 242 2 31 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 242 (accept_3_2 61 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 242 2 30 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 242 2 29 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 242 2 28 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 242 (accept_3_2 55 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 242 2 27 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 242 (Polychromatic418967fa.accept_20_13_18_2_1_10452 53 138 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 242 2 26 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 242 2 25 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 242 (accept_3_2 49 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 242 2 24 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 242 2 23 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 242 2 22 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 242 (accept_3_2 43 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 242 2 21 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 242 2 20 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 242 2 19 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 242 (accept_3_2 37 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 242 2 18 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 242 2 17 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 242
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 242 2 16 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 242 (accept_3_2 31 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 242 2 15 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 242 2 14 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 242 2 13 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 242 (accept_3_2 25 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 242 2 12 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 242 2 11 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 242 2 10 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 242 (accept_3_2 19 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 242 2 9 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 242 (Polychromatic418967fa.accept_19_17_5_14_1_3587 17 138 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 242 2 8 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 242 2 7 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 242 (accept_3_2 13 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 242 2 6 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 242 2 5 69 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 242 2 4 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 242 (accept_3_2 7 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  242 2 3 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 242 2 2 69 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 138 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 242 2 1 69 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 242 (accept_3_2 1 138 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 137 242 (Eq.refl Bool.true) (allA_succ_of_accept 105 137 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 137 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 242 (accept_3_2 103 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 137 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 242
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 101 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 137 242 (accept_3_2 100 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 242 (Polychromatic418967fa.accept_20_18_17_2_1_5941 98 137
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 242 (accept_3_2 97 137
  242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 242 (accept_3_2 94 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 242 (Polychromatic418967fa.accept_12_8_5_2_1_746
  92 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 242 (accept_3_2 91
  137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 242
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 90 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 137 242 (Polychromatic418967fa.accept_10_9_7_2_1_887 89 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 242 (accept_3_2 88 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 242 (Polychromatic418967fa.accept_9_5_2_8_1_109
  86 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 242 (accept_3_2 85
  137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 84 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 242 (accept_3_2 82 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 242 (Polychromatic418967fa.accept_12_8_5_2_1_746
  80 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 242 (accept_3_2 79
  137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 78 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 137 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 242 (accept_3_2 76 137 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 242 (Polychromatic418967fa.accept_10_4_7_2_1_211
  74 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 242 (accept_3_2 73
  137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 242
  (Polychromatic418967fa.accept_19_15_4_14_1_6400 72 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 242 (accept_3_2 70 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 242 (accept_3_2 67 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 242 (Polychromatic418967fa.accept_10_5_7_2_1_516 65 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 242 (accept_3_2 64 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 242
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 62 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 242 (accept_3_2 61 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 242 (accept_3_2 58 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 242 (accept_3_2 55 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 242 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 242 (Polychromatic418967fa.accept_13_1_7_8_1_1796 53 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 242 (accept_3_2 52 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 242 (accept_3_2 49 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 242 (accept_3_2 46 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 242
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 242 (accept_3_2 43 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 242 (accept_3_2 40 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 242
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 38 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 242 (accept_3_2 37 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 242 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 242 (accept_3_2 34 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 242 (accept_3_2 31 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 242 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 242 (accept_3_2 28 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 242
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 26 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 242 (accept_3_2 25 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 242 (accept_3_2 22 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 242 (accept_3_2 19 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 242 (Polychromatic418967fa.accept_19_18_4_14_1_14577 18 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 242 (Polychromatic418967fa.accept_16_1_9_2_1_4161 17 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 242 (accept_3_2 16 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 242 (accept_3_2 13 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 242 (accept_3_2 10 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 242
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 242 (accept_3_2 7 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 242 (accept_3_2 4 137 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 242
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 242 (accept_3_2 1 137 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 136 242 (Eq.refl Bool.true) (allA_of_3_0 107 136 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 135 242 (Eq.refl Bool.true) (allA_succ_of_accept 107 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 242 (accept_3_2 106 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 242 (accept_3_2 103 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 102 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 242 (accept_3_2 100 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 135 242 (Polychromatic418967fa.accept_19_4_2_14_1_10651 99 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 135 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 98 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 242 (accept_3_2 97 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 242 (accept_3_2 94 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 135 242 (Polychromatic418967fa.accept_13_1_5_8_1_207 92 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 242 (accept_3_2 91 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 242 (accept_3_2 88 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 242 (Polychromatic418967fa.accept_10_7_5_2_1_880 87 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 86 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 242 (accept_3_2 85 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 242 (Polychromatic418967fa.accept_19_8_2_14_1_3640 84 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 242 (accept_3_2 82 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 242 (Polychromatic418967fa.accept_19_4_2_14_1_10651 80 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 242 (accept_3_2 79 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 242 (accept_3_2 76 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 242 (Polychromatic418967fa.accept_19_17_2_14_1_11897 74 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 242 (accept_3_2 73 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 242 (accept_3_2 70 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 242 (accept_3_2 67 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 242 (accept_3_2 64 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 242 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 242 (accept_3_2 61 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 242 (Polychromatic418967fa.accept_16_12_7_2_1_4159 60 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 242 (accept_3_2 58 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 242 (Polychromatic418967fa.accept_17_5_16_4_1_4734 56 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 242 (accept_3_2 55 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 242 (accept_3_2 52 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 242 (Polychromatic418967fa.accept_13_12_5_8_1_1101 51 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 242 (Polychromatic418967fa.accept_19_12_2_14_1_10618 50 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 242 (accept_3_2 49 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 242 (accept_3_2 46 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 242 (accept_3_2 43 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 242 (accept_3_2 40 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 242 (Polychromatic418967fa.accept_17_5_16_4_1_4734 39 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 242 (accept_3_2 37 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 242 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 242 (accept_3_2 34 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 242 (Polychromatic418967fa.accept_17_15_16_4_1_2418 32 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 242 (accept_3_2 31 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 242 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 135
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 242 (accept_3_2 28 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 242 (accept_3_2 25 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 242 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 242 (accept_3_2 22 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 242 (accept_3_2 19 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 242 (accept_3_2 16 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 242 (Polychromatic418967fa.accept_17_15_16_4_1_2418 15 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 242 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 242 (accept_3_2 13 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 242 (accept_3_2 10 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 242 (accept_3_2 7 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 242 (accept_3_2 4 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 242 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 135 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 242 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 242 (accept_3_2 1 135 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 134 242 (Eq.refl Bool.true) (allA_succ_of_gcd 108 134 242 2 54 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 134 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 107 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 134 242 2 53 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 134 242 (Polychromatic418967fa.accept_16_9_6_2_1_3101 105 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 134 242 2 52 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 134 242 (accept_3_2 103 134 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 134 242 2 51 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 134 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 101 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 134 242 2 50 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 134 242 (Polychromatic418967fa.accept_16_3_6_2_1_4157 99 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 134 242 2 49 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 134 242 (accept_3_2 97 134 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 134 242 2 48 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 134 242
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 95 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 134 242 2 47 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 134 242 (Polychromatic418967fa.accept_15_3_14_2_1_1888 93 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 134 242 2 46 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 134 242 (accept_3_2 91 134 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 134 242 2 45 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 134 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 89 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 134 242 2 44 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 134 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 134 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 134 242 2 43 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 134 242 (accept_3_2 85 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 134 242 2 42 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 134 242 (Polychromatic418967fa.accept_16_3_6_2_1_4157
  83 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 242 2 41 67 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 242
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 81 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 242 2 40 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 242 (accept_3_2 79 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 242 2 39 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 242 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 134 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 242 2 38 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 242 2 37 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 242 (accept_3_2 73 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 242 2 36 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 242 (Polychromatic418967fa.accept_31_9_10_25_1_14576 71 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 242 2 35 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 242
  (Polychromatic418967fa.accept_25_19_9_17_1_14575 69 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 134 242 2 34 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 134 242 (accept_3_2 67 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 242 2 33 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 242 (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 242 2 32 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 242
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 242 2 31 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 242 (accept_3_2 61 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 242 2 30 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 134 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 242 2 29 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 242 2 28 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 242 (accept_3_2 55 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 242 2 27 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 242 (Polychromatic418967fa.accept_14_11_8_4_1_2628 53 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 242 2 26 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 242
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 51 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 242 2 25 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 242 (accept_3_2 49 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 242 2 24 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 134 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 242 2 23 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 242
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 242 2 22 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 242 (accept_3_2 43 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 242 2 21 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 242 (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 242 2 20 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 242
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 242 2 19 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 242 (accept_3_2 37 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 242 2 18 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 242 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 242 2 17 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 242
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 242 2 16 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 242 (accept_3_2 31 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 242 2 15 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 242 (Polychromatic418967fa.accept_19_10_1_14_1_9224 29 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 242 2 14 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 242
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 242 2 13 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 242 (accept_3_2 25 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 242 2 12 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 242 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 242 2 11 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 242
  (Polychromatic418967fa.accept_19_2_1_14_1_3663 21 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 242 2 10 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 242 (accept_3_2 19 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 242 2 9 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 134 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 242 2 8 67 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 242
  (Polychromatic418967fa.accept_19_15_1_14_1_14574 15 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 134 242 2 7 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 134 242 (accept_3_2 13 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 242 2 6 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 242 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 242 2 5 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 242
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 242 2 4 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 242 (accept_3_2 7 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  242 2 3 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 242 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 242 2 2 67 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 242 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 134 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 242 2 1 67 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 242 (accept_3_2 1 134 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 133 242 (Eq.refl Bool.true) (allA_of_3_0 110 133 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 132 242 (Eq.refl Bool.true) (allA_succ_of_gcd 110 132 242 22 5 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 242 (accept_3_2 109 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 242 2 54 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 242 (Polychromatic418967fa.accept_7_2_6_4_1_29
  107 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 132 242 2 53 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 132 242
  (Polychromatic418967fa.accept_17_3_13_4_1_8530 105 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 132 242 2 52 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 132 242 (accept_3_2 103 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 132 242 2 51 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 132 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 132 242 2 50 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 132 242 11 9 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 242 2 49 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 242 (accept_3_2 97
  132 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 242 2 48 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 242
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 242 2 47 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 242 2 46 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 242 (accept_3_2 91 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 242 2 45 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 89
  132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 242 22 4 6 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 242 2 43 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 242 (accept_3_2 85 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 242 2 42 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 242 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 242 2 41 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 242
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 81 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 242 2 40 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 242 (accept_3_2 79 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 242 2 39 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 132 242 11 7 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 132 242 2 38 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 242 2 37 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 242 (accept_3_2 73
  132 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 132 242 2 36 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 132 242
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 71 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 242 2 35 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 242 (Polychromatic418967fa.accept_20_9_12_2_1_5935 69 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 242 2 34 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 242 (accept_3_2 67 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 242 22 3 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 242 2 32 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 242 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 242 2 31 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 242 (accept_3_2 61 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 132 242 2 30 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 242 2 29 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 242 2 28 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 132 242 11 5 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 132 242 2 27 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 242
  (Polychromatic418967fa.accept_19_15_18_14_1_3564 53 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 132 242 2 26 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 132 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 242 2 25 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 242 (accept_3_2 49 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 242 2 24 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 242 2 23 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 242 22 2 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 242 (accept_3_2 43 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 242 2 21 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 242 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 242 2 20 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 242
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 242 2 19 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 242 (accept_3_2 37 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 242 2 18 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 242 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 242 2 17 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 242 11 3 12 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 242 2 16 66 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 242
  (accept_3_2 31 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 242 2 15 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 242
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 242 2 14 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 242 (Polychromatic418967fa.accept_18_9_6_8_1_2989 27 132 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 242 2 13 66 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 242 (accept_3_2 25 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 242 2 12 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 242 22 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 132 242 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 242 2 10 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 242 (accept_3_2 19 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 242 2 9 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 242 2 8 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 242
  (Polychromatic418967fa.accept_19_15_18_14_1_3564 15 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 242 2 7 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 242 (accept_3_2 13 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 242 2 6 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 132 242 11 1 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 242 2 5 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 242 2 4 66 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 242 (accept_3_2 7
  132 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 242 2 3 66 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 242 2 2 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 242 2 1 66 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 242 (accept_3_2 1 132 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 131 242 (Eq.refl Bool.true) (allA_succ_of_accept 111 131 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 131 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 131 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 242 (accept_3_2 109 131 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 131 242 (Polychromatic418967fa.accept_29_21_15_10_1_14573 108 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 107 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 131 242 (accept_3_2 106 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 242 (accept_3_2 103 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 131
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 131 242 (accept_3_2 100 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 131 242 (Polychromatic418967fa.accept_13_7_1_8_1_1778 98 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 242 (accept_3_2 97 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 242
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 242 (accept_3_2 94 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 242 (accept_3_2 91 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 242 (accept_3_2 88 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 242 (accept_3_2 85 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 242
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 242 (accept_3_2 82 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 242 (accept_3_2 79 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 242 (accept_3_2 76 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 242 (accept_3_2 73 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 242
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 242 (accept_3_2 70 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 242 (accept_3_2 67 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 242 (accept_3_2 64 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 242 (accept_3_2 61 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 242
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 242 (accept_3_2 58 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 242 (accept_3_2 55 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 242 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 242 (accept_3_2 52 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 242 (accept_3_2 49 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 242 (accept_3_2 46 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 242 (accept_3_2 43 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 242 (accept_3_2 40 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 242 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 242 (accept_3_2 37 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 242
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 242 (accept_3_2 34 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 242 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 242 (accept_3_2 31 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 242 (accept_3_2 28 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 242 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 242 (accept_3_2 25 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 242 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 242
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 242 (accept_3_2 22 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 242 (accept_3_2 19 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 242 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 242 (accept_3_2 16 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 242 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 242 (accept_3_2 13 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 242 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 242
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 242 (accept_3_2 10 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 242 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 242 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 242 (accept_3_2 7 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 242 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 242
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 242 (accept_3_2 4 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 242 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 242 (accept_3_2 1 131 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 130 242 (Eq.refl Bool.true) (allA_of_3_0 113 130 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 129 242 (Eq.refl Bool.true) (allA_succ_of_accept 113 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 242 (accept_3_2 112 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 129 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 242 (accept_3_2 109 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 242 (Polychromatic418967fa.accept_13_4_12_8_1_197 108 129
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 242 (accept_3_2 106 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 104 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 242 (accept_3_2 103 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 102 129
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 242 (accept_3_2 100 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 242 (Polychromatic418967fa.accept_13_7_12_8_1_199 98 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 242 (accept_3_2 97 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 242 (accept_3_2 94 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 242 (Polychromatic418967fa.accept_19_17_15_14_1_3623 93 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 242 (accept_3_2 91 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 242 (accept_3_2 88 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 242 (accept_3_2 85 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 242 (Polychromatic418967fa.accept_18_12_3_8_1_6817 84 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 242 (accept_3_2 82 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 242 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 242 (Polychromatic418967fa.accept_19_4_15_14_1_10614 80 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 242 (accept_3_2 79 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 242 (accept_3_2 76 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 242 (accept_3_2 73 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 242 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 242 (accept_3_2 70 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 242 (accept_3_2 67 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 242 (accept_3_2 64 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 242 (accept_3_2 61 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 242 (accept_3_2 58 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 242 (accept_3_2 55 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 242 (accept_3_2 52 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 242 (accept_3_2 49 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 242 (accept_3_2 46 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 242 (Polychromatic418967fa.accept_17_11_10_4_1_5955 45 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 242 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 242 (accept_3_2 43 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 242 (accept_3_2 40 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 242 (accept_3_2 37 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 242 (accept_3_2 34 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 242 (accept_3_2 31 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 242 (accept_3_2 28 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 242 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 242 (accept_3_2 25 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 242 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 242 (accept_3_2 22 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 242 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 242 (accept_3_2 19 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 242 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 242 (accept_3_2 16 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 242 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 242 (accept_3_2 13 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 242 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 129 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 242 (accept_3_2 10 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 242 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 242 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 242 (accept_3_2 7 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 242 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 242
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 242 (accept_3_2 4 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 242 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 242 (accept_3_2 1 129 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 128 242 (Eq.refl Bool.true) (allA_succ_of_gcd 114 128 242 2 57 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 128 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 128 242 2 56 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 128 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 128 242 2 55 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 128 242 (accept_3_2 109 128 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 128 242 2 54 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 128 242
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 107 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 128 242 2 53 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 128 242 (Polychromatic418967fa.accept_9_6_2_8_1_592 105 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 128 242 2 52 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 128 242 (accept_3_2 103 128 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 128 242 2 51 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 128 242
  (Polychromatic418967fa.accept_12_5_8_2_1_309 101 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 128 242 2 50 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 128 242 (Polychromatic418967fa.accept_15_9_8_2_1_1109 99 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 128 242 2 49 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 128 242 (accept_3_2 97 128 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 128 242 2 48 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 128 242
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 128 242 2 47 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 128 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 128 242 2 46 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 128 242 (accept_3_2 91 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 128 242 2 45 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 89
  128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 242 2 44 64 121 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 242 2 43 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 242 (accept_3_2 85 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 242 2 42 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 242 2 41 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 242
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 81 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 242 2 40 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 242 (accept_3_2 79 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 242 2 39 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 242 2 38 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 242 2 37 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 242 (accept_3_2 73 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 242 2 36 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 242 2 35 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 242 2 34 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 242 (accept_3_2 67 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 242 2 33 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 242 2 32 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 242
  (Polychromatic418967fa.accept_17_12_9_4_1_5982 63 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 242 2 31 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 242 (accept_3_2 61 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 242 2 30 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 242 2 29 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 242 2 28 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 242 (accept_3_2 55 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 242 2 27 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 242 2 26 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 242 2 25 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 242 (accept_3_2 49 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 242 2 24 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 242 2 23 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 242
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 242 2 22 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 242 (accept_3_2 43 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 242 2 21 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 242 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 242 2 20 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 242 2 19 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 242 (accept_3_2 37 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 242 2 18 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 242 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 242 2 17 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 242
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 242 2 16 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 242 (accept_3_2 31 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 242 2 15 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 242 2 14 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 242
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 242 2 13 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 242 (accept_3_2 25 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 242 2 12 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 242 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 242 2 11 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 242
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 242 2 10 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 242 (accept_3_2 19 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 242 2 9 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 242 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 128 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 242 2 8 64 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 242
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 242 2 7 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 242 (accept_3_2 13 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 242 2 6 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 242 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 242 2 5 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 242
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 242 2 4 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 242 (accept_3_2 7 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  242 2 3 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 242 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 242 2 2 64 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 128 242 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 128 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 242 2 1 64 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 242 (accept_3_2 1 128 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 127 242 (Eq.refl Bool.true) (allA_of_3_0 116 127 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 126 242 (Eq.refl Bool.true) (allA_succ_of_gcd 116 126 242 2 58 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 242 (accept_3_2 115 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 126 242 2 57 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128
  113 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 242 2 56 63 121
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 126 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 111 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 126 242 2 55 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 126 242 (accept_3_2 109 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 242 2 54 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 242 (Polychromatic418967fa.accept_13_3_9_8_1_4202 107 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 242 2 53 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 105 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 242 2 52 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 242 (accept_3_2 103 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 242 2 51 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 101 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 242 2 50 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 99 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 242 2 49 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 242 (accept_3_2 97 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 242 2 48 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 242 (Polychromatic418967fa.accept_13_4_9_8_1_1736 95 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 242 2 47 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 93 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 242 2 46 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 242 (accept_3_2 91 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 242 2 45 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 242 (Polychromatic418967fa.accept_13_11_9_8_1_1125 89 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 242 2 44 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 242 2 43 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 242 (accept_3_2 85 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 242 2 42 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 83 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 242 2 41 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 242 2 40 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 242 (accept_3_2 79 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 242 2 39 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 242 (Polychromatic418967fa.accept_13_12_9_8_1_2595 77 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 242 2 38 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 242 2 37 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 242 (accept_3_2 73 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 242 2 36 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 126 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 242 2 35 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 242 2 34 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 242 (accept_3_2 67 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 242 2 33 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 242 (Polychromatic418967fa.accept_17_14_7_4_1_3476 65 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 242 2 32 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 242 2 31 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 242 (accept_3_2 61 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 242 2 30 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 242 (Polychromatic418967fa.accept_13_7_9_8_1_188 59 126 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 242 2 29 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 242 2 28 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 242 (accept_3_2 55 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 242 2 27 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 242 (Polychromatic418967fa.accept_13_1_9_8_1_1734 53 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 242 2 26 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 242 2 25 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 242 (accept_3_2 49 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 242 2 24 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 242 (Polychromatic418967fa.accept_19_9_12_14_1_4966 47 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 242 2 23 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 242 2 22 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 242 (accept_3_2 43 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 242 2 21 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 126 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 242 2 20 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 242 2 19 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 242 (accept_3_2 37 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 242 2 18 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 242 (Polychromatic418967fa.accept_19_16_12_14_1_10640 35 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 242 2 17 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 242 2 16 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 242 (accept_3_2 31 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 242 2 15 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 242 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 242 2 14 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 242 2 13 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 242 (accept_3_2 25 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 242 2 12 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 242 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 242 2 11 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 242
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 242 2 10 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 242 (accept_3_2 19 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 242 2 9 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 242 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 242 2 8 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 242
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 242 2 7 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 242 (accept_3_2 13 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 242 2 6 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 242 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 242 2 5 63 121 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 242
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 242 2 4 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 242 (accept_3_2 7 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  242 2 3 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 242 (Polychromatic418967fa.accept_27_5_18_26_1_6827 5 126 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 242 2 2 63 121 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 242 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 242 2 1 63 121 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 242 (accept_3_2 1 126 242
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  242)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 125 242 (Eq.refl Bool.true) (allA_succ_of_accept 117 125 242
  (Polychromatic418967fa.accept_6_3_5_2_1_12 117 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 116 125 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 125 242 (accept_3_2 115 125 242 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 114 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 125 242
  (Polychromatic418967fa.accept_10_3_5_2_1_38 113 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 125 242 (accept_3_2 112 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 110 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 125 242 (accept_3_2 109 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 125 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 125
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 125 242 (accept_3_2 106 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 104 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 242 (accept_3_2 103 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 125 242 (Polychromatic418967fa.accept_15_12_5_2_1_2786 102
  125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 101 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 125 242 (accept_3_2 100 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 125 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 98 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 242 (accept_3_2 97 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 242 (accept_3_2 94 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 92 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 242 (accept_3_2 91 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 242 (Polychromatic418967fa.accept_17_5_6_4_1_8607 90 125
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 242 (accept_3_2 88 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 242 (accept_3_2 85 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 242 (Polychromatic418967fa.accept_20_4_5_2_1_3119 84 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 242 (accept_3_2 82 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 242 (accept_3_2 79 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 242
  (Polychromatic418967fa.accept_10_7_5_2_1_880 77 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 242 (accept_3_2 76 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 242 (Polychromatic418967fa.accept_15_14_5_2_1_4761 74 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 242 (accept_3_2 73 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 242 (accept_3_2 70 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 242 (accept_3_2 67 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 242
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 242 (accept_3_2 64 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 242 (Polychromatic418967fa.accept_17_11_6_4_1_4729 62 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 242 (accept_3_2 61 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 242 (Polychromatic418967fa.accept_19_3_11_14_1_7838 60 125
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 242 (accept_3_2 58 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 242 (accept_3_2 55 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 242
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 242 (accept_3_2 52 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 242 (Polychromatic418967fa.accept_20_10_5_2_1_3102 50 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 242 (accept_3_2 49 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 125
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 242 (accept_3_2 46 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 242 (accept_3_2 43 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 242 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 242
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 242 (accept_3_2 40 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 242 (accept_3_2 37 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 242 (Polychromatic418967fa.accept_17_2_6_4_1_2431 36 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 242 (accept_3_2 34 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 242 (accept_3_2 31 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 242
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 242 (accept_3_2 28 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 242 (accept_3_2 25 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 242 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 242 (accept_3_2 22 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 242 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 242 (accept_3_2 19 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 125
  242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 242
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 242 (accept_3_2 16 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 242 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 242 (accept_3_2 13 125 242 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 242 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 242
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 242 (accept_3_2 10 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 242 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 242 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 242 (accept_3_2 7 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 242 (Polychromatic418967fa.accept_19_6_11_14_1_10624 6 125 242
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 242
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 242 (accept_3_2 4 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 242 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 242 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 242 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 242 (accept_3_2 1 125 242 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 124 242 (Eq.refl Bool.true) (allA_of_3_0 119 124 242 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (Polychromatic418967fa.branch_242_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


