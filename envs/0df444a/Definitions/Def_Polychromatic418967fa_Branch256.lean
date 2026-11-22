-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch256
-- name    : Polychromatic418967fa_Branch256
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:52.288043+00:00
-- url     : https://prove2.me/theorems/4b4c58d9-a625-42ae-be7e-68c532c45095
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch256_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_256 : allB 256 256 :=
  allB_succ' 2 255 256 (Eq.refl Bool.true) (allA_succ_of_accept 1 255 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  255 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 256)) (allB_succ' 3 254 256
  (Eq.refl Bool.true) (allA_of_3_1 3 254 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 253 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 253 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 253 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 256 (accept_3_3 2 253 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 253 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 253 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 256)))) (allB_succ' 5 252 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 252 256 4 1 63 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 252 256 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 252 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 256 2 1 126 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 256 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  252 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 256))))) (allB_succ' 6 251 256
  (Eq.refl Bool.true) (allA_of_3_1 6 251 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 250 256 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 250 256 2 3 125 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 250 256 (accept_3_3 5 250 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 250 256 2 2 125 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 250 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 250 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 250 256 2 1 125 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 250 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 256))))))) (allB_succ' 8 249 256 (Eq.refl Bool.true) (allA_succ_of_accept 7 249 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 249 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 249 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 249 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 256 (accept_3_3 5 249 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 249 256 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 249 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  249 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 256 (accept_3_3 2 249
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 249 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 256)))))))) (allB_succ' 9 248 256
  (Eq.refl Bool.true) (allA_of_3_1 9 248 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 247 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 247 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 247 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 256 (accept_3_3 8 247 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 247 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 247 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 256 (accept_3_3 5 247 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 256 (Polychromatic418967fa.accept_25_4_22_6_1_13762 4 247 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 247 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 256 (accept_3_3 2 247 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 247 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 256)))))))))) (allB_succ' 11 246 256 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 246 256 2 5 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 246 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 246 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 246 256 2 4 123 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 246 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 256 2 3 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 256 (accept_3_3 5 246 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 246 256 2 2 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 246 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 246 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 246 256 2 1 123 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 246 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 256))))))))))) (allB_succ' 12 245 256 (Eq.refl Bool.true) (allA_of_3_1 12 245 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 244 256 (Eq.refl Bool.true) (allA_succ_of_gcd 12 244 256 4 3 61 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 244 256 (accept_3_3 11
  244 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 244 256 2 5 122 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 244 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 244 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 244 256 4 2 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 244 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 244 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 244 256 2 3 122 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 256 (accept_3_3 5 244 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 256 4 1 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 244 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 244 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 256 2 1 122 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 256
  (Polychromatic418967fa.accept_11_1_2_3_1_688 1 244 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 244 256))))))))))))) (allB_succ' 14 243 256 (Eq.refl Bool.true) (allA_succ_of_accept 13 243 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 243 256 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 243 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 256 (accept_3_3 11 243 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 243 256 (Polychromatic418967fa.accept_19_10_15_9_1_396 10 243 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 256
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 243 256 (accept_3_3 8 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  243 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 243 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 243 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 256 (accept_3_3 5 243 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 256 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 243 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 256
  (Polychromatic418967fa.accept_19_3_15_9_1_4576 3 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 256 (accept_3_3 2 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 243 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 256)))))))))))))) (allB_succ' 15 242 256 (Eq.refl Bool.true) (allA_of_3_1 15 242 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 241 256 (Eq.refl Bool.true) (allA_succ_of_accept 15 241 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 241 256 (accept_3_3 14 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 241 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 241 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 241 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 241 256 (accept_3_3 11 241 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 241 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 241 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 241 256 (accept_3_3 8 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  241 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 241 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 241 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 256 (accept_3_3 5 241 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 256 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 241 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 256 (accept_3_3 2 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 241 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 256)))))))))))))))) (allB_succ' 17 240 256 (Eq.refl Bool.true) (allA_succ_of_gcd 16 240 256
  16 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 240
  256 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 240 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 240 256 2 7 120 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 240 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 240 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 256 4 3 60 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 256 (accept_3_3 11 240 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 256 2 5 120 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 256
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 240 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 240 256 8 1 30 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 240 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 240 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 256 2 3 120 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 256 (accept_3_3 5 240 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 256 4 1 60 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 240 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 240 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 256 2 1 120 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 240 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 256))))))))))))))))) (allB_succ' 18 239 256 (Eq.refl Bool.true) (allA_of_3_1 18 239 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 238 256 (Eq.refl Bool.true) (allA_succ_of_gcd 18 238 256 2 9 119 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 238 256
  (accept_3_3 17 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 238 256 2 8 119 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 238 256
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 238 256 2 7 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 238 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 238 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 238 256 2 6 119 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 238 256 (accept_3_3 11 238 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 238 256 2 5 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 238 256 (Polychromatic418967fa.accept_24_9_22_16_1_826
  9 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 238 256 2 4 119 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 238 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 238 256 2 3 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 238 256 (accept_3_3 5 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 256 2 2 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 238 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 256 2 1 119 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 238 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 256))))))))))))))))))) (allB_succ' 20 237 256 (Eq.refl Bool.true) (allA_succ_of_accept 19 237 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 237 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 237 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 256 (accept_3_3 17 237 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 237 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 237 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 256 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 256 (accept_3_3 14
  237 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 256
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 237 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 237 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 256 (accept_3_3 11 237 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 237 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 237 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 256 (accept_3_3 8 237
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 237 256 (accept_3_3 5 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  237 256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 237 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 237 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 237 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 256 (accept_3_3 2 237 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 237 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 256)))))))))))))))))))) (allB_succ' 21 236 256
  (Eq.refl Bool.true) (allA_of_3_1 21 236 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 235 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 235 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 235 256 (accept_3_3 20 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 235 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 235 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 235 256
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 235 256 (accept_3_3 17 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 235 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 235 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 256 (accept_3_3 14 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 256 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 235 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 256 (accept_3_3 11 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 256 (accept_3_3 8 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 235 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 256 (accept_3_3 5 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 235 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 256 (accept_3_3 2 235 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 235 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 256)))))))))))))))))))))) (allB_succ' 23 234 256
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 234 256 2 11 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 234 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 234 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 256 2 10 117 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 256
  (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 256 2 9 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 256 (accept_3_3 17 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 256 2 8 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 234 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 234 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 256 2 7 117 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 256 2 6 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 256 (accept_3_3 11 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 256 2 5 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 234 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 256 2 4 117 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 256
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 256 2 3 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 256 (accept_3_3 5 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 256 2 2 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 234 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 256 2 1 117 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 234 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 256))))))))))))))))))))))) (allB_succ' 24 233 256 (Eq.refl Bool.true) (allA_of_3_1 24 233 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 232 256 (Eq.refl Bool.true) (allA_succ_of_gcd 24 232 256 8 3 29 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 232 256
  (accept_3_3 23 232 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 232 256 2 11 116 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 232 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 232 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 232 256 4 5 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 232 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 232 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 232 256 2 9 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 232 256 (accept_3_3 17 232 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 232 256 8 2 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 232 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 232 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 256 2 7 116 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 232 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 256 4 3 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 232 256 (accept_3_3 11 232 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  232 256 2 5 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 232 256 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 232 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 256 8 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 256 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 232 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 256 2 3 116 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 256 (accept_3_3 5
  232 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 256 4 1 58 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 232 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 232 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 232 256 2 1 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 232 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 232 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 256))))))))))))))))))))))))) (allB_succ' 26 231 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 231 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 256
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 231 256 (accept_3_3 23 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 231 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 231 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 256 (accept_3_3 20 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 231 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 231 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 231 256 (accept_3_3 17 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 231 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 231 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 231 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 256 (accept_3_3 14 231 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 231 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 231 256 (accept_3_3 11 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 231 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 231 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 256 (accept_3_3 8 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 231 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 231 256 (accept_3_3 5 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  231 256 (Polychromatic418967fa.accept_23_4_1_3_1_12431 4 231 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 231 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 256 (accept_3_3 2 231 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 231 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 256)))))))))))))))))))))))))) (allB_succ' 27 230 256
  (Eq.refl Bool.true) (allA_of_3_1 27 230 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 229 256 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 229 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 256 (accept_3_3 26 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 229 256 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 229 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 256
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 229 256 (accept_3_3 23 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 256 (accept_3_3 20 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 256 (Polychromatic418967fa.accept_20_19_9_16_1_2744 19 229 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 256
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 256 (accept_3_3 17 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 256 (accept_3_3 14 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 229 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 256
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 256 (accept_3_3 11 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 256 (accept_3_3 8 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 229 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 256 (accept_3_3 5 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 256 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 229 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 256 (accept_3_3 2 229 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 229 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 256)))))))))))))))))))))))))))) (allB_succ' 29 228
  256 (Eq.refl Bool.true) (allA_succ_of_gcd 28 228 256 4 7 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 228 256 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 228 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 228 256 2 13 114 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 256 4 6 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 228 256 (accept_3_3 23 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  228 256 2 11 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 228 256 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 228 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 256 4 5 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 19
  228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 256 2 9 114 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 256 (accept_3_3 17
  228 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 256 4 4 57 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 228 256 2 7 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 228 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 228 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 256 4 3 57 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 256 (accept_3_3 11 228 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 256 2 5 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 256 (Polychromatic418967fa.accept_18_9_12_4_1_1659
  9 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 256 4 2 57 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 256 2 3 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 228 256 (accept_3_3 5 228 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 228 256 4 1 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 228 256 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 228 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 256 2 1 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  228 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 256)))))))))))))))))))))))))))))
  (allB_succ' 30 227 256 (Eq.refl Bool.true) (allA_of_3_1 30 227 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 226 256 (Eq.refl Bool.true) (allA_succ_of_gcd 30 226 256 2 15 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 226 256 (accept_3_3 29 226 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 226 256 2 14 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 226 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 256 2 13 113 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 256 2 12 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 256 (accept_3_3 23 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 256 2 11 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 226 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 256 2 10 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 256 2 9 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 256 (accept_3_3 17 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 256 2 8 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 226 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 256 2 7 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 256 2 6 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 256 (accept_3_3 11 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 256 2 5 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 256 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 226 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 256 2 4 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 256
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 256 2 3 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 256 (accept_3_3 5 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 256 2 2 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 226 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 256 2 1 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 226 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 256))))))))))))))))))))))))))))))) (allB_succ' 32 225 256 (Eq.refl Bool.true) (allA_succ_of_accept 31
  225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 225 256 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 225 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 256 (accept_3_3 29 225 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 256 (Polychromatic418967fa.accept_24_4_9_16_1_15608 28 225
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 256
  (Polychromatic418967fa.accept_19_8_16_9_1_8847 27 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 256 (accept_3_3 26 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 256 (accept_3_3 23 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 256 (Polychromatic418967fa.accept_17_5_4_1_1_3369 22 225 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 256
  (Polychromatic418967fa.accept_10_1_5_6_1_649 21 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 256 (accept_3_3 20 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 256 (accept_3_3 17 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 256 (Polychromatic418967fa.accept_22_16_5_14_1_9301 16 225 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 256
  (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 256 (accept_3_3 14 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 225 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 256 (accept_3_3 11 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 225 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 256
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 256 (accept_3_3 8 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 256 (accept_3_3 5 225 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 225 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 256 (accept_3_3 2 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 256)))))))))))))))))))))))))))))))) (allB_succ' 33 224 256 (Eq.refl Bool.true) (allA_of_3_1
  33 224 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 223 256 (Eq.refl Bool.true) (allA_succ_of_accept 33
  223 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 223 256 (accept_3_3 32 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 223 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 223 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 223 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 223 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 256 (accept_3_3 29 223 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 256 (accept_3_3 26 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 256 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 256 (accept_3_3 23 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 256 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 223 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 256 (accept_3_3 20 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 223 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 256 (accept_3_3 17 223 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 223 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 256 (accept_3_3 14 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 256 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 256 (accept_3_3 11 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 223 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 256 (accept_3_3 8 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 256 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 256 (accept_3_3 5 223 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 256 (Polychromatic418967fa.accept_19_4_14_9_1_10227 4 223 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 256 (accept_3_3 2 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 223 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 256)))))))))))))))))))))))))))))))))) (allB_succ' 35 222 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 222 256 2 17 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 222 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 222 256 2 16 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 256
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 256 2 15 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 256 (accept_3_3 29 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 256 2 14 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 222 256 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 256 2 13 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 256 2 12 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 256 (accept_3_3 23 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 256 2 11 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 222 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 256 2 10 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 256
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 256 2 9 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 256 (accept_3_3 17 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 256 2 8 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 256 2 7 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 256 2 6 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 256 (accept_3_3 11 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 256 2 5 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 256 2 4 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 256
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 256 2 3 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 256 (accept_3_3 5 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 256 2 2 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 222 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 256 2 1 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 222 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 256))))))))))))))))))))))))))))))))))) (allB_succ' 36 221 256 (Eq.refl Bool.true) (allA_of_3_1 36 221
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 220 256 (Eq.refl Bool.true) (allA_succ_of_gcd 36 220 256 4
  9 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 220
  256 (accept_3_3 35 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 220 256 2 17 110 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 220 256
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 220 256 4 8 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 220 256 (Polychromatic418967fa.accept_28_3_24_4_1_15649 31 220 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 256 2 15 110 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 256 (accept_3_3 29
  220 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 256 4 7 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 220 256 2 13 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 220 256 (Polychromatic418967fa.accept_23_2_13_3_1_3942 25 220 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 220 256 4 6 55 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 256 (accept_3_3 23 220 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 256 2 11 110 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 256
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 220 256 4 5 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 220 256 (Polychromatic418967fa.accept_17_2_16_1_1_2260 19 220 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 220 256 2 9 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 220 256 (accept_3_3 17 220 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 220 256 4 4 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 220 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 220 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 256 2 7 110 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 220 256 4 3 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 220 256 (accept_3_3 11 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  220 256 2 5 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 220 256 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 220 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 256 4 2 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 256 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 220 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 256 2 3 110 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 256 (accept_3_3 5
  220 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 256 4 1 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 256
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 220 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 256 2 1 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 220 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 256))))))))))))))))))))))))))))))))))))) (allB_succ' 38 219 256
  (Eq.refl Bool.true) (allA_succ_of_accept 37 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 256
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 219 256 (accept_3_3 35 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 219 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 219 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 256 (accept_3_3 32 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 256 (accept_3_3 29 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 256 (accept_3_3 26 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 256
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 256 (accept_3_3 23 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 256 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 256 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 256 (accept_3_3 20 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 256
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 256 (accept_3_3 17 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 219 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 256 (accept_3_3 14 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 256
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 219 256 (accept_3_3 11 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 219 256 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 219 256 (Polychromatic418967fa.accept_17_9_15_1_1_7048 9 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 256 (accept_3_3 8 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 219 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 256
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 219 256 (accept_3_3 5 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  219 256 (Polychromatic418967fa.accept_19_4_10_9_1_4569 4 219 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 219 256 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 256 (accept_3_3 2 219 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 219 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 256))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 218 256 (Eq.refl Bool.true) (allA_of_3_1 39 218 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 217 256 (Eq.refl Bool.true) (allA_succ_of_accept 39 217 256 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 256 (accept_3_3 38
  217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 217 256
  (Polychromatic418967fa.accept_19_18_8_9_1_3325 37 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 217 256 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 217 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 256 (accept_3_3 35 217 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 217 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33
  217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 256 (accept_3_3 32
  217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 256
  (Polychromatic418967fa.accept_10_1_7_6_1_91 31 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 217 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 217 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 256 (accept_3_3 29 217 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 217 256 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 256 (accept_3_3 26 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 256 (accept_3_3 23 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 256 (accept_3_3 20 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 256 (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 256 (Polychromatic418967fa.accept_19_18_8_9_1_3325 18 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 256 (accept_3_3 17 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 217 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 256 (accept_3_3 14 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 256 (accept_3_3 11 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 256 (accept_3_3 8 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 256 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 256 (accept_3_3 5 217 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 256 (Polychromatic418967fa.accept_19_4_8_9_1_10211 4 217 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 256 (accept_3_3 2 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 217 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 256)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 216 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 216 256 8 5 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 216 256 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 216 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 216 256 2 19 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 256 (Polychromatic418967fa.accept_7_2_6_4_1_29 37
  216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 256 4 9 54 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 256 (accept_3_3 35
  216 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 256 2 17 108 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 256
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 256 8 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 216 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 216 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 256 2 15 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 256 (accept_3_3 29 216 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 256 4 7 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 256 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 216
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 256 2 13 108 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 256
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 256 8 3 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 256 (accept_3_3 23 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  216 256 2 11 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 216 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 216 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 256 4 5 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 256 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 256 2 9 108 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 256 (accept_3_3 17
  216 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 256 8 2 27 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 256
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 216 256 2 7 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 216 256 (Polychromatic418967fa.accept_17_13_12_1_1_4524 13 216 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 256 4 3 54 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 256 (accept_3_3 11 216 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 256 2 5 108 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 256
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 256 8 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 216 256 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 216 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 256 2 3 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 256 (accept_3_3 5 216 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 256 4 1 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 216 256 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 256 2 1 108 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 256
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 216 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 256))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 215 256 (Eq.refl Bool.true) (allA_of_3_1 42
  215 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 214 256 (Eq.refl Bool.true) (allA_succ_of_gcd 42 214
  256 2 21 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 214 256 (accept_3_3 41 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 214 256 2 20 107 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 214 256
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 214 256 2 19 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 214 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 214 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 214 256 2 18 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 214 256 (accept_3_3 35 214 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 214 256 2 17 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 214 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 256 2 16 107 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 256 2 15 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 256 (accept_3_3 29 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 256 2 14 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 256 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 214 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 256 2 13 107 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 256
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 256 2 12 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 256 (accept_3_3 23 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 256 2 11 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 214 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 256 2 10 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 256 2 9 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 256 (accept_3_3 17 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 256 2 8 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 214 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 256 2 7 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 256
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 256 2 6 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 256 (accept_3_3 11 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 256 2 5 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 256 (Polychromatic418967fa.accept_17_9_10_1_1_3345 9 214 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 256 2 4 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 256
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 256 2 3 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 256 (accept_3_3 5 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 256 2 2 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 214 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 256 2 1 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 256
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 214 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 256))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 213 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 213 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 256 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 213 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 256 (accept_3_3 41 213 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 256 (Polychromatic418967fa.accept_11_7_4_3_1_302
  40 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 213 256 (accept_3_3 38 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 213 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 256 (accept_3_3 35 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 256
  (Polychromatic418967fa.accept_19_14_4_9_1_6009 33 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 213 256 (accept_3_3 32 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 213 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 256 (accept_3_3 29 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 256
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 256 (accept_3_3 26 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 256 (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 256 (accept_3_3 23 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 256 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 213 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 256 (accept_3_3 20 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 256 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 256 (accept_3_3 17 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 256 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 213 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 256
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 256 (accept_3_3 14 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 256 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 256 (accept_3_3 11 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 256 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 256
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 256 (accept_3_3 8 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 256 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 256 (accept_3_3 5 213 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 256 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 213 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 256
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 256 (accept_3_3 2 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 256)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 212 256 (Eq.refl Bool.true)
  (allA_of_3_1 45 212 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 211 256 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 211 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 256 (accept_3_3 44 211 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 211 256 (Polychromatic418967fa.accept_18_7_13_4_1_1670 43 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 256
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 256 (accept_3_3 41 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 256 (accept_3_3 38 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 256
  (Polychromatic418967fa.accept_19_17_2_9_1_4582 36 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 256 (accept_3_3 35 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 256 (accept_3_3 32 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 256
  (Polychromatic418967fa.accept_19_11_2_9_1_8897 30 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 256 (accept_3_3 29 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 256 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 256 (accept_3_3 26 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 256 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 256
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 256 (accept_3_3 23 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 256 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 256 (accept_3_3 20 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 256 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 256
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 256 (accept_3_3 17 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 256 (Polychromatic418967fa.accept_22_16_13_14_1_14009 16 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 256 (accept_3_3 14 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 256 (Polychromatic418967fa.accept_21_13_1_4_1_11182 13 211
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 256
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 256 (accept_3_3 11 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 256 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 256 (accept_3_3 8 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 256 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 256
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 256 (accept_3_3 5 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 256 (Polychromatic418967fa.accept_19_4_2_9_1_4584 4 211 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 256 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 256 (accept_3_3 2 211 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 256 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 211 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 256))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 210 256 (Eq.refl Bool.true) (allA_succ_of_gcd 46 210 256 2 23 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 210 256
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 210 256 2 22 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 210 256 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 210 256 2 21 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 210 256 (accept_3_3 41 210 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 256 2 20 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 256 (Polychromatic418967fa.accept_12_3_6_4_1_400
  39 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 210 256 2 19 105 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 256 2 18 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 256 (accept_3_3 35 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 210 256 2 17 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 210 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 210 256 2 16 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 256
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 256 2 15 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 256 (accept_3_3 29 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 256 2 14 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 210 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 256 2 13 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 256 2 12 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 256 (accept_3_3 23 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 256 2 11 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 210 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 256 2 10 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 256 2 9 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 256 (accept_3_3 17 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 256 2 8 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 210 256 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 256 2 7 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 256
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 256 2 6 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 256 (accept_3_3 11 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 256 2 5 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 256 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 256 2 4 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 256
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 256 2 3 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 256 (accept_3_3 5 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 256 2 2 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 256 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 210 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 256 2 1 105 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 256
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 210 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 256))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 209 256 (Eq.refl Bool.true)
  (allA_of_3_1 48 209 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 208 256 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 208 256 16 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 208 256 (accept_3_3 47 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 208 256 2 23 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 208 256 (Polychromatic418967fa.accept_22_1_10_14_1_10991 45 208 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 208 256 4 11 52 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 208 256
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 208 256 2 21 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 208 256 (accept_3_3 41 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 208 256 8 5 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 208 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 208 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 256 2 19 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 208 256 4 9 52 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 208 256 (accept_3_3 35
  208 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 208 256 2 17 104 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 208 256
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 208 256 16 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 208 256 (Polychromatic418967fa.accept_17_14_4_1_1_3341 31 208 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 208 256 2 15 104 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 208 256 (accept_3_3 29 208 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 208 256 4 7 52 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 208 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 208 256 2 13 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 208 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 208 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 208 256 8 3 26 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 256 (accept_3_3 23 208 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 256 2 11 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 256 (Polychromatic418967fa.accept_9_3_1_4_1_216 21
  208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 256 4 5 52 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 256
  (Polychromatic418967fa.accept_28_19_12_4_1_15648 19 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 208 256 2 9 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 208 256 (accept_3_3 17 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 256 16 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 208 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 256 2 7 104 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 256
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 256 4 3 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 208 256 (accept_3_3 11 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  208 256 2 5 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 208 256 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 208 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 256 8 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 256 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 208 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 256 2 3 104 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 256 (accept_3_3 5
  208 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 256 4 1 52 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 256
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 208 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 256 2 1 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 256 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 256)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 207 256 (Eq.refl Bool.true) (allA_succ_of_accept 49 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 256
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 48 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 207 256 (accept_3_3 47 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 207 256 (Polychromatic418967fa.accept_19_8_17_9_1_4542 46 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 207 256 (Polychromatic418967fa.accept_19_7_17_9_1_8879 45 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 256 (accept_3_3 44 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 256 (accept_3_3 41 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 256 (Polychromatic418967fa.accept_17_6_3_1_1_7011 40 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 256 (accept_3_3 38 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 256
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 256 (accept_3_3 35 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 256 (Polychromatic418967fa.accept_13_8_12_9_1_1168 34 207 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 207
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 256 (accept_3_3 32 207
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 256 (accept_3_3 29 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 256 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 256 (Polychromatic418967fa.accept_19_8_17_9_1_4542 27 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 256 (accept_3_3 26 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 256
  (Polychromatic418967fa.accept_21_3_18_4_1_11234 24 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 256 (accept_3_3 23 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 256 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 207 256 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 256 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 256 (accept_3_3 20 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 256
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 207 256 (accept_3_3 17 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 207 256 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 256 (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 256 (accept_3_3 14 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 256
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 256 (accept_3_3 11 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 256 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 256 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 207 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 256 (accept_3_3 8 207 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 256
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 256 (accept_3_3 5 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 256 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 207 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 256 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 207 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 256 (accept_3_3 2 207 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 256 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  256)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 206 256 (Eq.refl Bool.true) (allA_of_3_1 51 206
  256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 205 256 (Eq.refl Bool.true) (allA_succ_of_accept 51 205
  256 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 205 256 (accept_3_3 50 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 205 256 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 205 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 256 (accept_3_3 47 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 205 256 (accept_3_3 44 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 256 (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 256 (accept_3_3 41 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 256 (accept_3_3 38 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 205 256 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 256 (accept_3_3 35 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 205 256
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 256 (accept_3_3 32 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 256 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 256 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 256 (accept_3_3 29 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 256 (accept_3_3 26 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 205 256 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 205 256 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 256 (accept_3_3 23 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 256 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 256 (accept_3_3 20 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 256 (Polychromatic418967fa.accept_19_18_15_9_1_3310 18 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 256 (accept_3_3 17 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 256 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 205
  256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 256 (accept_3_3 14 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 256 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 256 (accept_3_3 11 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 256 (accept_3_3 8 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 256 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 256 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 256 (accept_3_3 5 205 256 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 256 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 205 256 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 256
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 256 (accept_3_3 2 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 256 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 205 256 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 256))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_256_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))


